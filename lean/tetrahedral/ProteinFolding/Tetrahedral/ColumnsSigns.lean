import ProteinFolding.Tetrahedral.BulkFoliation

/-! Face quadrants and the starting points of the columns in Lemma C. -/

namespace ProteinFolding.Tetrahedral

def columnOpposite (d : Fin 4) : Fin 4 :=
  if d = 0 then 1 else if d = 1 then 0 else if d = 2 then 3 else 2

def bigFaceY (d : Fin 4) : ℤ := bondComponent d 1
def bigFaceZ (d : Fin 4) : ℤ := bondComponent d 2

theorem columnOpposite_ne (d : Fin 4) : columnOpposite d ≠ d := by revert d; decide
theorem bigFaceY_unit (d : Fin 4) : bigFaceY d = 1 ∨ bigFaceY d = -1 := by revert d; decide
theorem bigFaceZ_unit (d : Fin 4) : bigFaceZ d = 1 ∨ bigFaceZ d = -1 := by revert d; decide

theorem bigFace_quadrant_direction (d : Fin 4) :
    bulkQuadrantDirection (bigFaceY d) (bigFaceZ d) = d := by revert d; decide

theorem smallFace_quadrant_direction (d : Fin 4) :
    bulkQuadrantDirection (-bigFaceY d) (-bigFaceZ d) = columnOpposite d := by revert d; decide

theorem big_dangling_quadrant (m : ℕ) {v : Site} (hvA : InASublattice v.val)
    (hv : v ∈ octahedron m) (d : Fin 4) (hout : step v d ∉ octahedron m) :
    1 ≤ bigFaceY d * bulkY m (step v d) ∧ 0 ≤ bigFaceZ d * bulkZ (step v d) := by
  have hf := (step_not_mem_octahedron_A m hvA hv d).mp hout
  have h := (inOctahedron_iff_A m hvA).mp ((mem_octahedron m v).mp hv)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  dsimp [bulkY, bulkZ]
  rw [step_val_of_A v hvA d]
  simp_rw [bondVector_eq_bondComponent]
  fin_cases d <;> dsimp [bigFaceY, bigFaceZ, bondComponent, tetraCoordinate] at hf h0 h1 h2 h3 ⊢
  all_goals constructor <;> omega

theorem small_dangling_quadrant (m : ℕ) {v : Site} (hvB : InBSublattice v.val)
    (hv : v ∈ octahedron m) (d : Fin 4) (hout : step v d ∉ octahedron m) :
    1 ≤ (-bigFaceY d) * bulkY m (step v d) ∧ 0 ≤ (-bigFaceZ d) * bulkZ (step v d) := by
  have hf := (step_not_mem_octahedron_B m hvB hv d).mp hout
  have h := (inOctahedron_iff_B m hvB).mp ((mem_octahedron m v).mp hv)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  dsimp [bulkY, bulkZ]
  rw [step_val_of_B v hvB d]
  simp_rw [bondVector_eq_bondComponent]
  fin_cases d <;> dsimp [bigFaceY, bigFaceZ, bondComponent, tetraCoordinate, octRadius] at hf h0 h1 h2 h3 ⊢
  all_goals constructor <;> omega

theorem dangling_tetraCoordinate_bounds (m : ℕ) {p : Site} (hp : IsDangling m p) (i : Fin 4) :
    -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m p.val i ∧
      tetraCoordinate m p.val i ≤ octRadius m + 3 := by
  obtain ⟨_, v, hv, hadj⟩ := hp
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step v p).mp hadj
  have h := (mem_octahedron m v).mp hv i
  rcases v.property with hvA | hvB
  · rw [tetraCoordinate_step_A m hvA]
    split_ifs <;> omega
  · rw [tetraCoordinate_step_B m hvB]
    split_ifs <;> omega

end ProteinFolding.Tetrahedral
