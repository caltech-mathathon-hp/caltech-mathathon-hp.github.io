import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization
import ProteinFolding.Tetrahedral.OctahedralEdgeUnion

/-!
# The three prescribed F' edges, Section 5.6(O7)

The y coordinate below is absolute, so its formula includes the centre's
offset R. Subtracting R gives the manuscript's displayed Y coordinate.
-/

namespace ProteinFolding.Tetrahedral

def entryEdgeFrame : OctEdgeFrame :=
  ⟨2, 3, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def exitEdgeFrame : OctEdgeFrame :=
  ⟨0, 3, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

def trackEdgeFrame : OctEdgeFrame :=
  ⟨1, 3, 0, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

def entryEdgeCoordinates (m r : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then (r % 2 : ℕ) else if k = 1 then octRadius m + r else -octRadius m + r

def exitEdgeCoordinates (m r : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then octRadius m - r else if k = 1 then octRadius m + r else -(r % 2 : ℕ)

def trackEdgeCoordinates (m r : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then r else if k = 1 then octRadius m + (r % 2 : ℕ) else -octRadius m + r

private theorem coordinates_eq_of_tetra_pair_sums (m : ℕ) (p q : Coordinates)
    (hx : tetraCoordinate m p 0 + tetraCoordinate m p 1 = 2 * q 0)
    (hy : tetraCoordinate m p 0 + tetraCoordinate m p 2 = 2 * (q 1 - octRadius m))
    (hz : tetraCoordinate m p 0 + tetraCoordinate m p 3 = 2 * q 2) : p = q := by
  have hpx := tetraCoordinate_pair_x m p
  have hpy := tetraCoordinate_pair_y m p
  have hpz := tetraCoordinate_pair_z m p
  funext k
  fin_cases k
  · change p 0 = q 0
    omega
  · change p 1 = q 1
    omega
  · change p 2 = q 2
    omega

theorem entryEdgeZigzag_coordinates {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (octEdgeZigzag m entryEdgeFrame r).val = entryEdgeCoordinates m r := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm entryEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2))).val 2 = octRadius m at hk
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2))).val 3 = -octRadius m at hj
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2))).val 0 = -octRadius m + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2))).val 1 = octRadius m - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [entryEdgeCoordinates]; omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm entryEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2) + 1)).val 2 = octRadius m - 1 at hk
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2) + 1)).val 3 = -octRadius m - 1 at hj
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2) + 1)).val 0 = -octRadius m + 3 + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m entryEdgeFrame (2 * (r / 2) + 1)).val 1 = octRadius m - 1 - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [entryEdgeCoordinates]; omega

theorem exitEdgeZigzag_coordinates {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (octEdgeZigzag m exitEdgeFrame r).val = exitEdgeCoordinates m r := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm exitEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2))).val 0 = octRadius m at hk
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2))).val 3 = -octRadius m at hj
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2))).val 2 = -octRadius m + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2))).val 1 = octRadius m - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [exitEdgeCoordinates]; omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm exitEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2) + 1)).val 0 = octRadius m - 1 at hk
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2) + 1)).val 3 = -octRadius m - 1 at hj
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2) + 1)).val 2 = -octRadius m + 3 + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m exitEdgeFrame (2 * (r / 2) + 1)).val 1 = octRadius m - 1 - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [exitEdgeCoordinates]; omega

theorem trackEdgeZigzag_coordinates {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (octEdgeZigzag m trackEdgeFrame r).val = trackEdgeCoordinates m r := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm trackEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2))).val 1 = octRadius m at hk
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2))).val 3 = -octRadius m at hj
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2))).val 0 = -octRadius m + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2))).val 2 = octRadius m - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [trackEdgeCoordinates]; omega
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq]
    obtain ⟨_, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm trackEdgeFrame (r / 2)
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2) + 1)).val 1 = octRadius m - 1 at hk
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2) + 1)).val 3 = -octRadius m - 1 at hj
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2) + 1)).val 0 = -octRadius m + 3 + 4 * (r / 2 : ℕ) at ha
    change tetraCoordinate m (octEdgeZigzag m trackEdgeFrame (2 * (r / 2) + 1)).val 2 = octRadius m - 1 - 4 * (r / 2 : ℕ) at hb
    apply coordinates_eq_of_tetra_pair_sums m
    all_goals dsimp [trackEdgeCoordinates]; omega

theorem deleted_edge_track_region (m : ℕ) {p : Site} (hp : bulkOnDeletedEdge m p)
    (hx : 3 ≤ p.val 0) (hz : p.val 2 ≤ -3) : OctEdgeSite m 1 3 p := by
  have ho : p ∈ octahedron m := by
    obtain ⟨_, _, _, h | h⟩ := hp
    · exact h.1.1
    · exact h.1.1
  rcases p.property with hpA | hpB
  · obtain ⟨k, j, hkj, hk, hj⟩ := (bulkOnDeletedEdge_A_iff m hpA ho).mp hp
    have h := (inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp ho)
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have hf : tetraCoordinate m p.val 1 = octRadius m ∧ tetraCoordinate m p.val 3 = -octRadius m := by
      fin_cases k <;> fin_cases j <;> dsimp [tetraCoordinate] at hk hj h0 h1 h2 h3 ⊢
      all_goals first | exact (hkj rfl).elim | (constructor <;> omega)
    exact Or.inl ⟨⟨ho, hpA, hf.1⟩, hf.2⟩
  · obtain ⟨k, j, hkj, hk, hj⟩ := (bulkOnDeletedEdge_B_iff m hpB ho).mp hp
    have h := (inOctahedron_iff_B m hpB).mp ((mem_octahedron m _).mp ho)
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have hf : tetraCoordinate m p.val 1 = 2 * (m : ℤ) - 3 ∧
        tetraCoordinate m p.val 3 = -(2 * (m : ℤ) - 1) := by
      fin_cases k <;> fin_cases j <;> dsimp [tetraCoordinate] at hk hj h0 h1 h2 h3 ⊢
      all_goals first | exact (hkj rfl).elim | (constructor <;> omega)
    exact Or.inr ⟨⟨ho, hpB, hf.2⟩, hf.1⟩

theorem deleted_edge_track_region_iff {m : ℕ} (hm : 1 ≤ m) (p : Site) :
    (bulkOnDeletedEdge m p ∧ 3 ≤ p.val 0 ∧ p.val 2 ≤ -3) ↔
      ∃ r : ℕ, 3 ≤ r ∧ r ≤ 2 * m - 5 ∧ p = octEdgeZigzag m trackEdgeFrame r := by
  constructor
  · rintro ⟨he, hx, hz⟩
    have hp := deleted_edge_track_region m he hx hz
    obtain ⟨r, hr, heq⟩ := (octEdgeSite_iff_param hm trackEdgeFrame p).mp hp
    refine ⟨r, ?_, ?_, heq⟩
    all_goals rw [heq, trackEdgeZigzag_coordinates hm] at hx hz
    all_goals dsimp [trackEdgeCoordinates, octRadius] at hx hz
    all_goals omega
  · rintro ⟨r, hr, hlast, rfl⟩
    have hrange : r < 2 * m - 1 := by omega
    refine ⟨⟨1, 3, by decide, octEdgeZigzag_mem hm trackEdgeFrame hrange⟩, ?_, ?_⟩
    all_goals rw [trackEdgeZigzag_coordinates hm]
    all_goals dsimp [trackEdgeCoordinates, octRadius]
    all_goals omega

end ProteinFolding.Tetrahedral
