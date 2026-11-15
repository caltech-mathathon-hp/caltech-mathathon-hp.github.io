import ProteinFolding.Tetrahedral.OctahedralLinkCounts

/-! Exterior paths and the cancellations forced by their two end bonds. -/

namespace ProteinFolding.Tetrahedral

structure OctExteriorLink (m n : ℕ) where
  site : ℕ → Site
  dir : ℕ → Fin 4
  length_ge_two : 2 ≤ n
  step_eq : ∀ i < n, site (i + 1) = step (site i) (dir i)
  start_mem : site 0 ∈ octahedron m
  end_mem : site n ∈ octahedron m
  interior_outside : ∀ i, 0 < i → i < n → site i ∉ octahedron m

namespace OctExteriorLink

/-- An ordinary adjacency path supplies direction labels automatically. -/
noncomputable def ofPath {m n : ℕ} (f : ℕ → Site) (hlen : 2 ≤ n)
    (hadj : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hs : f 0 ∈ octahedron m) (he : f n ∈ octahedron m)
    (hout : ∀ i, 0 < i → i < n → f i ∉ octahedron m) : OctExteriorLink m n where
  site := f
  dir := fun i => if hi : i < n then
    Classical.choose ((adj_iff_exists_step (f i) (f (i + 1))).mp (hadj i hi)) else 0
  length_ge_two := hlen
  step_eq := by
    intro i hi
    rw [dif_pos hi]
    exact (Classical.choose_spec ((adj_iff_exists_step (f i) (f (i + 1))).mp (hadj i hi))).symm
  start_mem := hs
  end_mem := he
  interior_outside := hout

variable {m n : ℕ} (L : OctExteriorLink m n)

def positive (r : Fin 4) : ℕ := positivePathCount L.site L.dir n r
def negative (r : Fin 4) : ℕ := negativePathCount L.site L.dir n r
def cancellations : ℕ := ∑ r : Fin 4, min (L.positive r) (L.negative r)

theorem min_le_cancellations (r : Fin 4) :
    min (L.positive r) (L.negative r) ≤ L.cancellations := by
  unfold cancellations
  exact Finset.single_le_sum (fun s _ => Nat.zero_le (min (L.positive s) (L.negative s)))
    (Finset.mem_univ r)

theorem first_outside : L.site 1 ∉ octahedron m :=
  L.interior_outside 1 (by omega) (by have h := L.length_ge_two; omega)

theorem last_outside : L.site (n - 1) ∉ octahedron m :=
  L.interior_outside (n - 1) (by have h := L.length_ge_two; omega)
    (by have h := L.length_ge_two; omega)

theorem last_step : L.site n = step (L.site (n - 1)) (L.dir (n - 1)) := by
  have hn := L.length_ge_two
  have h := L.step_eq (n - 1) (by omega)
  have heq : n - 1 + 1 = n := by omega
  simpa only [heq] using h

theorem reverse_last_step : step (L.site n) (L.dir (n - 1)) = L.site (n - 1) := by
  rw [L.last_step]
  exact step_step _ _

theorem first_big_face (hpA : InASublattice (L.site 0).val) :
    tetraCoordinate m (L.site 0).val (L.dir 0) = octRadius m := by
  apply (step_not_mem_octahedron_A m hpA L.start_mem (L.dir 0)).mp
  have h := L.step_eq 0 (by have hn := L.length_ge_two; omega)
  rw [← h]
  exact L.first_outside

theorem first_small_face (hpB : InBSublattice (L.site 0).val) :
    tetraCoordinate m (L.site 0).val (L.dir 0) = -(2 * (m : ℤ) - 1) := by
  apply (step_not_mem_octahedron_B m hpB L.start_mem (L.dir 0)).mp
  have h := L.step_eq 0 (by have hn := L.length_ge_two; omega)
  rw [← h]
  exact L.first_outside

theorem last_big_face (hqA : InASublattice (L.site n).val) :
    tetraCoordinate m (L.site n).val (L.dir (n - 1)) = octRadius m := by
  apply (step_not_mem_octahedron_A m hqA L.end_mem (L.dir (n - 1))).mp
  rw [L.reverse_last_step]
  exact L.last_outside

theorem last_small_face (hqB : InBSublattice (L.site n).val) :
    tetraCoordinate m (L.site n).val (L.dir (n - 1)) = -(2 * (m : ℤ) - 1) := by
  apply (step_not_mem_octahedron_B m hqB L.end_mem (L.dir (n - 1))).mp
  rw [L.reverse_last_step]
  exact L.last_outside

theorem coordinate_difference (r : Fin 4) :
    tetraCoordinate m (L.site n).val r = tetraCoordinate m (L.site 0).val r +
      4 * ((L.positive r : ℤ) - (L.negative r : ℤ)) -
      (siteCharge (L.site n) - siteCharge (L.site 0)) :=
  path_tetraCoordinate_difference m L.site L.dir n L.step_eq r

theorem first_A_cancelled (hpA : InASublattice (L.site 0).val) :
    L.positive (L.dir 0) ≤ L.negative (L.dir 0) := by
  have h := L.coordinate_difference (L.dir 0)
  have hf := L.first_big_face hpA
  rw [siteCharge_A hpA] at h
  rcases (L.site n).property with hqA | hqB
  · have he := ((inOctahedron_iff_A m hqA).mp ((mem_octahedron m _).mp L.end_mem) (L.dir 0)).2
    rw [siteCharge_A hqA] at h
    omega
  · have he := ((inOctahedron_iff_B m hqB).mp ((mem_octahedron m _).mp L.end_mem) (L.dir 0)).2
    rw [siteCharge_B hqB] at h
    dsimp [octRadius] at hf
    omega

theorem first_B_cancelled (hpB : InBSublattice (L.site 0).val) :
    L.negative (L.dir 0) ≤ L.positive (L.dir 0) := by
  have h := L.coordinate_difference (L.dir 0)
  have hf := L.first_small_face hpB
  rw [siteCharge_B hpB] at h
  rcases (L.site n).property with hqA | hqB
  · have he := ((inOctahedron_iff_A m hqA).mp ((mem_octahedron m _).mp L.end_mem) (L.dir 0)).1
    rw [siteCharge_A hqA] at h
    dsimp [octRadius] at he
    omega
  · have he := ((inOctahedron_iff_B m hqB).mp ((mem_octahedron m _).mp L.end_mem) (L.dir 0)).1
    rw [siteCharge_B hqB] at h
    omega

theorem last_A_cancelled (hqB : InBSublattice (L.site n).val) :
    L.positive (L.dir (n - 1)) ≤ L.negative (L.dir (n - 1)) := by
  have h := L.coordinate_difference (L.dir (n - 1))
  have hf := L.last_small_face hqB
  rw [siteCharge_B hqB] at h
  rcases (L.site 0).property with hpA | hpB
  · have hs := ((inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp L.start_mem) (L.dir (n - 1))).1
    rw [siteCharge_A hpA] at h
    dsimp [octRadius] at hs
    omega
  · have hs := ((inOctahedron_iff_B m hpB).mp ((mem_octahedron m _).mp L.start_mem) (L.dir (n - 1))).1
    rw [siteCharge_B hpB] at h
    omega

theorem last_B_cancelled (hqA : InASublattice (L.site n).val) :
    L.negative (L.dir (n - 1)) ≤ L.positive (L.dir (n - 1)) := by
  have h := L.coordinate_difference (L.dir (n - 1))
  have hf := L.last_big_face hqA
  rw [siteCharge_A hqA] at h
  rcases (L.site 0).property with hpA | hpB
  · have hs := ((inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp L.start_mem) (L.dir (n - 1))).2
    rw [siteCharge_A hpA] at h
    omega
  · have hs := ((inOctahedron_iff_B m hpB).mp ((mem_octahedron m _).mp L.start_mem) (L.dir (n - 1))).2
    rw [siteCharge_B hpB] at h
    dsimp [octRadius] at hf
    omega

theorem cancellations_ge_one : 1 ≤ L.cancellations := by
  have hs : min (L.positive (L.dir 0)) (L.negative (L.dir 0)) ≤ L.cancellations :=
    L.min_le_cancellations _
  rcases (L.site 0).property with hpA | hpB
  · have hc := L.first_A_cancelled hpA
    have hp := positivePathCount_ge_one L.site L.dir
      (by have hn := L.length_ge_two; omega : 0 < n) hpA
    change 1 ≤ L.positive (L.dir 0) at hp
    rw [Nat.min_eq_left hc] at hs
    omega
  · have hc := L.first_B_cancelled hpB
    have hp := negativePathCount_ge_one L.site L.dir
      (by have hn := L.length_ge_two; omega : 0 < n) hpB
    change 1 ≤ L.negative (L.dir 0) at hp
    rw [Nat.min_eq_right hc] at hs
    omega

theorem cancellations_ge_two_AB (hpA : InASublattice (L.site 0).val)
    (hqB : InBSublattice (L.site n).val) : 2 ≤ L.cancellations := by
  have hn := L.length_ge_two
  have hlastA : InASublattice (L.site (n - 1)).val := by
    have h := adj_sublattices (step_adj (L.site (n - 1)) (L.dir (n - 1)))
    rw [← L.last_step] at h
    rcases h with h | h
    · exact h.1
    · exact (sublattices_disjoint _ h.2 hqB).elim
  have h0 := L.first_A_cancelled hpA
  have he := L.last_A_cancelled hqB
  by_cases hdir : L.dir 0 = L.dir (n - 1)
  · have hp := positivePathCount_ge_two L.site L.dir (by omega : 0 < n)
      (by omega : n - 1 < n) (by omega : 0 ≠ n - 1) hpA hlastA hdir
    change 2 ≤ L.positive (L.dir 0) at hp
    have hs : min (L.positive (L.dir 0)) (L.negative (L.dir 0)) ≤ L.cancellations :=
      L.min_le_cancellations _
    rw [Nat.min_eq_left h0] at hs
    omega
  · have hp := positivePathCount_ge_one L.site L.dir (by omega : 0 < n) hpA
    have hq := positivePathCount_ge_one L.site L.dir (by omega : n - 1 < n) hlastA
    change 1 ≤ L.positive (L.dir 0) at hp
    change 1 ≤ L.positive (L.dir (n - 1)) at hq
    have hs := Finset.sum_le_sum_of_subset
      (Finset.subset_univ ({L.dir 0, L.dir (n - 1)} : Finset (Fin 4)))
      (f := fun r => min (L.positive r) (L.negative r))
    rw [Finset.sum_pair hdir, Nat.min_eq_left h0, Nat.min_eq_left he] at hs
    change L.positive (L.dir 0) + L.positive (L.dir (n - 1)) ≤ L.cancellations at hs
    omega

theorem cancellations_ge_two_BA (hpB : InBSublattice (L.site 0).val)
    (hqA : InASublattice (L.site n).val) : 2 ≤ L.cancellations := by
  have hn := L.length_ge_two
  have hlastB : InBSublattice (L.site (n - 1)).val := by
    have h := adj_sublattices (step_adj (L.site (n - 1)) (L.dir (n - 1)))
    rw [← L.last_step] at h
    rcases h with h | h
    · exact (sublattices_disjoint _ hqA h.2).elim
    · exact h.1
  have h0 := L.first_B_cancelled hpB
  have he := L.last_B_cancelled hqA
  by_cases hdir : L.dir 0 = L.dir (n - 1)
  · have hp := negativePathCount_ge_two L.site L.dir (by omega : 0 < n)
      (by omega : n - 1 < n) (by omega : 0 ≠ n - 1) hpB hlastB hdir
    change 2 ≤ L.negative (L.dir 0) at hp
    have hs : min (L.positive (L.dir 0)) (L.negative (L.dir 0)) ≤ L.cancellations :=
      L.min_le_cancellations _
    rw [Nat.min_eq_right h0] at hs
    omega
  · have hp := negativePathCount_ge_one L.site L.dir (by omega : 0 < n) hpB
    have hq := negativePathCount_ge_one L.site L.dir (by omega : n - 1 < n) hlastB
    change 1 ≤ L.negative (L.dir 0) at hp
    change 1 ≤ L.negative (L.dir (n - 1)) at hq
    have hs := Finset.sum_le_sum_of_subset
      (Finset.subset_univ ({L.dir 0, L.dir (n - 1)} : Finset (Fin 4)))
      (f := fun r => min (L.positive r) (L.negative r))
    rw [Finset.sum_pair hdir, Nat.min_eq_right h0, Nat.min_eq_right he] at hs
    change L.negative (L.dir 0) + L.negative (L.dir (n - 1)) ≤ L.cancellations at hs
    omega

end OctExteriorLink

theorem siteCharge_step (p : Site) (d : Fin 4) :
    siteCharge (step p d) = 1 - siteCharge p := by
  rcases p.property with hpA | hpB
  · rw [siteCharge_A hpA, siteCharge_B (step_in_B hpA d)]; omega
  · rw [siteCharge_B hpB, siteCharge_A (step_in_A hpB d)]; omega

theorem siteCharge_bounds (p : Site) : 0 ≤ siteCharge p ∧ siteCharge p ≤ 1 := by
  rcases p.property with hpA | hpB
  · rw [siteCharge_A hpA]; omega
  · rw [siteCharge_B hpB]; omega

theorem path_siteCharge_mod (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ)
    (hstep : ∀ i < n, f (i + 1) = step (f i) (d i)) :
    (siteCharge (f n) + (n : ℤ)) % 2 = siteCharge (f 0) := by
  induction n with
  | zero => have h := siteCharge_bounds (f 0); omega
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    have hs := siteCharge_step (f n) (d n)
    rw [← hstep n (by omega)] at hs
    push_cast
    omega

namespace OctExteriorLink

variable {m n : ℕ} (L : OctExteriorLink m n)

theorem cancellations_ge_two_odd_length (hn : n % 2 = 1) : 2 ≤ L.cancellations := by
  have hmod := path_siteCharge_mod L.site L.dir n L.step_eq
  rcases (L.site 0).property with hpA | hpB
  · rw [siteCharge_A hpA] at hmod
    rcases (L.site n).property with hqA | hqB
    · rw [siteCharge_A hqA] at hmod
      omega
    · exact L.cancellations_ge_two_AB hpA hqB
  · rw [siteCharge_B hpB] at hmod
    rcases (L.site n).property with hqA | hqB
    · exact L.cancellations_ge_two_BA hpB hqA
    · rw [siteCharge_B hqB] at hmod
      omega

end OctExteriorLink

end ProteinFolding.Tetrahedral
