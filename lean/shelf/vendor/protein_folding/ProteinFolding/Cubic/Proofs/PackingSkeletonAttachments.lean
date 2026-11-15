import ProteinFolding.Cubic.Proofs.PackingAttachmentDisjoint
import ProteinFolding.Cubic.Proofs.PackingSkeletonPrefix

/-! Any lifted E word supported on the cube skeleton avoids the bulk and
its approach. The first approach point's unique cube neighbour is the lower
top-face hole; later approach points are at distance at least two from the cube. -/

namespace ProteinFolding.CubicPackingSkeletonAttachments

open CubicPacking CubicCertificates CubicPackingGeometry CubicPackingLift CubicPackingBulk
open CubicPackingAttachments CubicPackingFaceBulkDisjoint

theorem no_skeleton_xz_interior (d : ℕ) (p : Site)
    (hx : 1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) (hz : 1 ≤ p 2 ∧ p 2 ≤ (d : ℤ)) :
    ¬ EdgeSkeleton (fun _ => 0) (d + 2) p := by
  rintro ⟨_, i, j, hij, hi, hj⟩
  have hnormal (k : Fin 3) (hk : BoundaryCoordinate (fun _ => 0) p (d + 2) k) : k = 1 := by
    fin_cases k <;> dsimp [BoundaryCoordinate] at hk <;> first | rfl | omega
  exact hij ((hnormal i hi).trans (hnormal j hj).symm)

theorem no_skeleton_face (d : ℕ) (f : CubicPackingFrameFaces.Face) (p : Site)
    (hp : CubicPackingFrameFaces.HSupport d f p) : ¬ EdgeSkeleton (fun _ => 0) (d + 2) p := by
  rintro ⟨_, i, j, hij, hi, hj⟩
  cases f <;> dsimp [CubicPackingFrameFaces.HSupport] at hp
  all_goals fin_cases i <;> fin_cases j <;> dsimp [BoundaryCoordinate] at hi hj <;> first | contradiction | omega

theorem lowerHole_not_skeleton (d : ℕ) (hd : 2 ≤ d) :
    ¬ EdgeSkeleton (fun _ => 0) (d + 2) (lowerHole d) := by
  apply no_skeleton_xz_interior
  · dsimp [lowerHole, CubicPackingRouting.point]; omega
  · dsimp [lowerHole, CubicPackingRouting.point]; omega

theorem approach_far_of_positive (d alpha : ℕ) (j : Fin (alpha + 8)) (hj : 0 < j.val) :
    (d : ℤ) + 2 < approachPos d alpha j 1 ∨ approachPos d alpha j 2 = -2 := by
  unfold approachPos approachPoint
  split_ifs <;> dsimp [CubicPackingRouting.point] <;> omega

theorem skeleton_not_adjacent_approach (d alpha : ℕ) (hd : 2 ≤ d) (p : Site)
    (hp : EdgeSkeleton (fun _ => 0) (d + 2) p) (j : Fin (alpha + 8)) :
    ¬ cubicLattice.Adj (approachPos d alpha j) p := by
  intro ha
  by_cases hj : j.val = 0
  · have hhole : lowerHole d ∈ cube (fun _ => 0) (d + 2) := by
      intro k
      fin_cases k <;> dsimp [lowerHole, CubicPackingRouting.point] <;> omega
    have hstep : cubicLattice.Adj (approachPos d alpha j) (lowerHole d) := by
      rw [approachPos_first d alpha j hj]
      change latticeDistance _ _ = 1
      rw [distance_eq]
      simp [lowerHole, CubicPackingRouting.point]
    have he := cube_exterior_neighbour_unique (fun _ => 0) (d + 2)
      (approachPos d alpha j) p (lowerHole d)
      (approachPos_not_mem_cube d alpha j) hp.1 hhole ha hstep
    exact lowerHole_not_skeleton d hd (he ▸ hp)
  · have hfar := approach_far_of_positive d alpha j (by omega)
    obtain ⟨dir, he⟩ := adj_step ha
    have hbounds := step_coordinate_bounds (approachPos d alpha j) dir
    have hy := hp.1 1
    have hz := hp.1 2
    rw [← he] at hy hz
    have hby := hbounds 1
    have hbz := hbounds 2
    dsimp only at hy hz
    omega

theorem skeleton_E_approach_disjoint (d alpha t : ℕ) (hd : 2 ≤ d)
    (f : Fold cubicLattice (edgeWord t).length)
    (hH : ∀ i, (edgeWord t).get i = .H → EdgeSkeleton (fun _ => 0) (d + 2) (f.pos i))
    (i : Fin (edgeWord t).length) (j : Fin (alpha + 8)) :
    f.pos i ≠ (approachFold d alpha).pos j := by
  intro he
  change f.pos i = approachPos d alpha j at he
  cases hi : (edgeWord t).get i with
  | H => exact approachPos_not_mem_cube d alpha j (he ▸ (hH i hi).1)
  | P =>
    obtain ⟨k, hk, hik⟩ := edgeWord_P_has_H_neighbour t f i hi
    apply skeleton_not_adjacent_approach d alpha hd (f.pos k) (hH k hk) j
    exact he ▸ hik

theorem skeleton_E_bulk_disjoint (d t : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (f : Fold cubicLattice (edgeWord t).length)
    (hH : ∀ i, (edgeWord t).get i = .H → EdgeSkeleton (fun _ => 0) (d + 2) (f.pos i))
    (hP : ∀ i, (edgeWord t).get i = .P → f.pos i ∉ cube (fun _ => 0) (d + 2))
    (i : Fin (edgeWord t).length) (j : Fin (d ^ 3 + 2)) :
    f.pos i ≠ (bulkFold d (by omega) heven).pos j := by
  intro he
  cases hi : (edgeWord t).get i with
  | H =>
    have hb := bulk_bounds d (by omega) heven j
    exact no_skeleton_xz_interior d _ hb.1 hb.2.2 (he ▸ hH i hi)
  | P => exact hP i hi (he.symm ▸ bulkFold_in_cube d (by omega) heven j)

theorem skeleton_E_bulkApproachWord_disjoint (d alpha t : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (f : Fold cubicLattice (edgeWord t).length)
    (hH : ∀ i, (edgeWord t).get i = .H → EdgeSkeleton (fun _ => 0) (d + 2) (f.pos i))
    (hP : ∀ i, (edgeWord t).get i = .P → f.pos i ∉ cube (fun _ => 0) (d + 2))
    (i : Fin (edgeWord t).length) (j : Fin (bulkApproachWord d alpha).length) :
    f.pos i ≠ (bulkApproachWordFold d alpha (by omega) heven).pos j :=
  disjoint_bulkApproachWord_of d alpha (by omega) heven _
    (skeleton_E_bulk_disjoint d t hd heven f hH hP i)
    (skeleton_E_approach_disjoint d alpha t hd f hH i) j

end ProteinFolding.CubicPackingSkeletonAttachments
