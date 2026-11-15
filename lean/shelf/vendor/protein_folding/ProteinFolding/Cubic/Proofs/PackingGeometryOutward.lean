import ProteinFolding.Cubic.Proofs.PackingGeometryExterior
import ProteinFolding.Cubic.Proofs.PackingGeometryFaces

/-! Outward directions for lifting compressed E paths. Each skeleton site
has two outward choices, and adjacent skeleton sites share two such choices. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

theorem boundary_outward_plane (a p : Site) (n : ℕ) (k : Fin 3)
    (hb : BoundaryCoordinate a p n k) :
    ∃ d : Fin 6, directionAxis d = k ∧
      ∀ r : Site, r k = p k → step r d ∉ cube a n := by
  fin_cases k <;> rcases hb with hb | hb
  all_goals simp only [Fin.reduceFinMk] at hb ⊢
  all_goals first
    | refine ⟨0, rfl, ?_⟩
      intro r he hmem
      have h := hmem 0
      simp only [step, ↓reduceIte] at h
      omega
    | refine ⟨1, rfl, ?_⟩
      intro r he hmem
      have h := hmem 0
      simp only [step, ↓reduceIte] at h
      omega
    | refine ⟨2, rfl, ?_⟩
      intro r he hmem
      have h := hmem 1
      simp only [step, ↓reduceIte] at h
      omega
    | refine ⟨3, rfl, ?_⟩
      intro r he hmem
      have h := hmem 1
      simp only [step, ↓reduceIte] at h
      omega
    | refine ⟨4, rfl, ?_⟩
      intro r he hmem
      have h := hmem 2
      simp only [step, ↓reduceIte] at h
      omega
    | refine ⟨5, rfl, ?_⟩
      intro r he hmem
      have h := hmem 2
      simp only [step, ↓reduceIte] at h
      omega

theorem common_outward_of_planes (a p q : Site) (n : ℕ) (i j : Fin 3) (hij : i ≠ j)
    (hi : BoundaryCoordinate a p n i) (hj : BoundaryCoordinate a p n j)
    (hqi : q i = p i) (hqj : q j = p j) :
    ∃ d e : Fin 6, d ≠ e ∧ step p d ∉ cube a n ∧ step q d ∉ cube a n ∧
      step p e ∉ cube a n ∧ step q e ∉ cube a n := by
  obtain ⟨d, hdi, hd⟩ := boundary_outward_plane a p n i hi
  obtain ⟨e, hej, he⟩ := boundary_outward_plane a p n j hj
  have hde : d ≠ e := by
    intro h
    have heq := congrArg directionAxis h
    rw [hdi, hej] at heq
    exact hij heq
  exact ⟨d, e, hde, hd p rfl, hd q hqi, he p rfl, he q hqj⟩

theorem skeleton_two_outward (a p : Site) (n : ℕ) (hp : EdgeSkeleton a n p) :
    ∃ d e : Fin 6, d ≠ e ∧ step p d ∉ cube a n ∧ step p e ∉ cube a n := by
  obtain ⟨_, i, j, hij, hi, hj⟩ := hp
  obtain ⟨d, e, hde, hd, _, he, _⟩ := common_outward_of_planes a p p n i j hij hi hj rfl rfl
  exact ⟨d, e, hde, hd, he⟩

theorem skeleton_boundary_pairs (a p : Site) (n : ℕ) (hp : EdgeSkeleton a n p) :
    (BoundaryCoordinate a p n 0 ∧ BoundaryCoordinate a p n 1) ∨
    (BoundaryCoordinate a p n 0 ∧ BoundaryCoordinate a p n 2) ∨
    (BoundaryCoordinate a p n 1 ∧ BoundaryCoordinate a p n 2) := by
  obtain ⟨_, i, j, hij, hi, hj⟩ := hp
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.reduceFinMk] at hi hj hij
  all_goals first | exact False.elim (hij rfl) | tauto

set_option maxHeartbeats 500000 in
/-- Adjacent points of the cube skeleton share the two exterior normals of
their geometric edge, including corner-to-edge transitions and side two. -/
theorem adjacent_skeleton_common_outward (a p q : Site) (n : ℕ)
    (hp : EdgeSkeleton a n p) (hq : EdgeSkeleton a n q) (hadj : cubicLattice.Adj p q) :
    ∃ d e : Fin 6, d ≠ e ∧ step p d ∉ cube a n ∧ step q d ∉ cube a n ∧
      step p e ∉ cube a n ∧ step q e ∉ cube a n := by
  obtain ⟨dir, rfl⟩ := adj_step hadj
  have hpairs := skeleton_boundary_pairs a p n hp
  have hqpairs := skeleton_boundary_pairs a (step p dir) n hq
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hq0 := hq.1 0
  have hq1 := hq.1 1
  have hq2 := hq.1 2
  fin_cases dir
  all_goals simp only [BoundaryCoordinate, step, Fin.reduceFinMk, ↓reduceIte] at hpairs hqpairs hq0 hq1 hq2
  all_goals first
    | apply common_outward_of_planes a p _ n 1 2 (by decide)
      · unfold BoundaryCoordinate; omega
      · unfold BoundaryCoordinate; omega
      · simp [step]
      · simp [step]
    | apply common_outward_of_planes a p _ n 0 2 (by decide)
      · unfold BoundaryCoordinate; omega
      · unfold BoundaryCoordinate; omega
      · simp [step]
      · simp [step]
    | apply common_outward_of_planes a p _ n 0 1 (by decide)
      · unfold BoundaryCoordinate; omega
      · unfold BoundaryCoordinate; omega
      · simp [step]
      · simp [step]

end ProteinFolding.CubicPackingGeometry
