import ProteinFolding.Tetrahedral.OctahedralZigzags

/-! The edge has precisely 2m−1 sites, in the stated zigzag order. -/

namespace ProteinFolding.Tetrahedral

theorem octEdgeZigzag_even_mem {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) {n : ℕ}
    (hn : n < m) : OctAEdgeSite m F.k F.j (octEdgeZigzag m F (2 * n)) := by
  obtain ⟨hpA, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm F n
  refine ⟨⟨?_, hpA, hk⟩, hj⟩
  rw [mem_octahedron, inOctahedron_iff_A m hpA]
  intro i
  rcases F.index_cases i with rfl | rfl | rfl | rfl
  all_goals dsimp [octRadius] at *; constructor <;> omega

theorem octEdgeZigzag_odd_mem {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) {n : ℕ}
    (hn : n < m - 1) : OctBEdgeSite m F.k F.j (octEdgeZigzag m F (2 * n + 1)) := by
  obtain ⟨hpB, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm F n
  refine ⟨⟨?_, hpB, ?_⟩, ?_⟩
  · rw [mem_octahedron, inOctahedron_iff_B m hpB]
    intro i
    rcases F.index_cases i with rfl | rfl | rfl | rfl
    all_goals dsimp [octRadius] at *; constructor <;> omega
  · dsimp [octRadius] at hj
    omega
  · dsimp [octRadius] at hk
    omega

theorem octAEdgeSite_iff_param {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (p : Site) :
    OctAEdgeSite m F.k F.j p ↔ ∃ n < m, p = octEdgeZigzag m F (2 * n) := by
  constructor
  · rintro ⟨⟨hp, hpA, hk⟩, hj⟩
    have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m p).mp hp)
    have ha := h F.a
    have hs := tetraCoordinate_sum_frame m F p.val
    have hc := tetraCoordinate_mod_A m hpA F.a
    let n : ℕ := ((tetraCoordinate m p.val F.a + octRadius m) / 4).toNat
    have hparam : tetraCoordinate m p.val F.a = -octRadius m + 4 * (n : ℤ) := by
      dsimp [n, octRadius] at *
      omega
    have hn : n < m := by
      dsimp [octRadius] at *
      omega
    refine ⟨n, hn, ?_⟩
    obtain ⟨_, hk', hj', ha', hb'⟩ := octEdgeZigzag_even hm F n
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext i
    rcases F.index_cases i with rfl | rfl | rfl | rfl
    all_goals omega
  · rintro ⟨n, hn, rfl⟩
    exact octEdgeZigzag_even_mem hm F hn

theorem octBEdgeSite_iff_param {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (p : Site) :
    OctBEdgeSite m F.k F.j p ↔ ∃ n < m - 1, p = octEdgeZigzag m F (2 * n + 1) := by
  constructor
  · rintro ⟨⟨hp, hpB, hj⟩, hk⟩
    have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m p).mp hp)
    have ha := h F.a
    have hb := h F.b
    have hs := tetraCoordinate_sum_frame m F p.val
    have hc := tetraCoordinate_mod_B m hpB F.a
    let n : ℕ := ((tetraCoordinate m p.val F.a + octRadius m - 3) / 4).toNat
    have hparam : tetraCoordinate m p.val F.a = -octRadius m + 3 + 4 * (n : ℤ) := by
      dsimp [n, octRadius] at *
      omega
    have hn : n < m - 1 := by
      dsimp [octRadius] at *
      omega
    refine ⟨n, hn, ?_⟩
    obtain ⟨_, hk', hj', ha', hb'⟩ := octEdgeZigzag_odd hm F n
    apply Subtype.ext
    apply tetraCoordinate_injective m
    funext i
    rcases F.index_cases i with rfl | rfl | rfl | rfl
    all_goals dsimp [octRadius] at *; omega
  · rintro ⟨n, hn, rfl⟩
    exact octEdgeZigzag_odd_mem hm F hn

theorem octEdgeZigzag_mem {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) {r : ℕ}
    (hr : r < 2 * m - 1) : OctEdgeSite m F.k F.j (octEdgeZigzag m F r) := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq]
    exact Or.inl (octEdgeZigzag_even_mem hm F (by omega))
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq]
    exact Or.inr (octEdgeZigzag_odd_mem hm F (by omega))

theorem octEdgeSite_iff_param {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (p : Site) :
    OctEdgeSite m F.k F.j p ↔ ∃ r < 2 * m - 1, p = octEdgeZigzag m F r := by
  constructor
  · rintro (hp | hp)
    · obtain ⟨n, hn, rfl⟩ := (octAEdgeSite_iff_param hm F p).mp hp
      exact ⟨2 * n, by omega, rfl⟩
    · obtain ⟨n, hn, rfl⟩ := (octBEdgeSite_iff_param hm F p).mp hp
      exact ⟨2 * n + 1, by omega, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact octEdgeZigzag_mem hm F hr

theorem octEdgeZigzag_height {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) :
    octEdgeHeight4 m F.a F.b (octEdgeZigzag m F r) =
      -2 * octRadius m + 4 * (r : ℤ) := by
  induction r with
  | zero =>
    obtain ⟨_, _, _, ha, hb⟩ := octEdgeStart_spec hm F
    change tetraCoordinate m (octEdgeStart m F).val F.a -
      tetraCoordinate m (octEdgeStart m F).val F.b = -2 * octRadius m + 4 * (0 : ℤ)
    omega
  | succ r ih =>
    rw [octEdgeZigzag_succ, edgeForwardStep_height m F.ab]
    push_cast
    omega

theorem octEdgeZigzag_injective {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) :
    Function.Injective (octEdgeZigzag m F) := by
  intro r s heq
  have h := congrArg (octEdgeHeight4 m F.a F.b) heq
  rw [octEdgeZigzag_height hm F, octEdgeZigzag_height hm F] at h
  omega

def octEdgeSites (m : ℕ) (F : OctEdgeFrame) : Finset Site :=
  Finset.univ.image (fun r : Fin (2 * m - 1) => octEdgeZigzag m F r.val)

theorem mem_octEdgeSites {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (p : Site) :
    p ∈ octEdgeSites m F ↔ OctEdgeSite m F.k F.j p := by
  rw [octEdgeSite_iff_param hm F]
  constructor
  · intro hp
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hp
    exact ⟨r.val, r.isLt, hr.symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_univ _, rfl⟩

theorem octEdgeSites_card {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) :
    (octEdgeSites m F).card = 2 * m - 1 := by
  unfold octEdgeSites
  have hinj : Function.Injective (fun r : Fin (2 * m - 1) => octEdgeZigzag m F r.val) := by
    intro r s heq
    exact Fin.ext (octEdgeZigzag_injective hm F heq)
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem octEdgeZigzag_adj_iff {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r s : ℕ) :
    tetrahedralLattice.Adj (octEdgeZigzag m F r) (octEdgeZigzag m F s) ↔
      r + 1 = s ∨ s + 1 = r := by
  constructor
  · intro hadj
    have hbounds := octEdgeHeight4_adj_bounds m F.a F.b hadj
    rw [octEdgeZigzag_height hm F, octEdgeZigzag_height hm F] at hbounds
    have hne : r ≠ s := by
      intro heq
      subst s
      exact tetrahedralLattice.loopless _ hadj
    omega
  · rintro (rfl | heq)
    · exact octEdgeZigzag_adj m F r
    · rw [← heq]
      exact (octEdgeZigzag_adj m F s).symm

/-- The full edge zigzag is a shortest path in the entire lattice. -/
theorem octEdgeZigzag_path_length_lower_bound {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hstart : f 0 = octEdgeZigzag m F 0)
    (hend : f n = octEdgeZigzag m F (2 * m - 2)) : 2 * m - 2 ≤ n := by
  have hb := path_height_upper_bound m F.a F.b f n hstep
  rw [hstart, hend, octEdgeZigzag_height hm F, octEdgeZigzag_height hm F] at hb
  dsimp [octRadius] at hb
  omega

/-- A shortest path between the ends of the edge is exactly its zigzag. -/
theorem octEdgeZigzag_unique_geodesic {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (f : ℕ → Site)
    (hstep : ∀ i < 2 * m - 2, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hstart : f 0 = octEdgeZigzag m F 0)
    (hend : f (2 * m - 2) = octEdgeZigzag m F (2 * m - 2)) :
    ∀ i ≤ 2 * m - 2, f i = octEdgeZigzag m F i := by
  apply saturated_path_unique m F.a F.b f (octEdgeZigzag m F) (2 * m - 2)
    hstep (fun i _ => octEdgeZigzag_adj m F i) _ _ hstart
  · rw [hstart, hend, octEdgeZigzag_height hm F, octEdgeZigzag_height hm F]
    omega
  · rw [octEdgeZigzag_height hm F, octEdgeZigzag_height hm F]
    omega

end ProteinFolding.Tetrahedral
