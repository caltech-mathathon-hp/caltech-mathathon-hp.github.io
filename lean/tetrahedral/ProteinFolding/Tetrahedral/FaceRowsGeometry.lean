import ProteinFolding.Tetrahedral.FaceCoordinates
import ProteinFolding.Tetrahedral.Skins
import ProteinFolding.Tetrahedral.BulkFoliation

/-! The two F' layers of each skin and their three row bonds, Lemma R(a). -/

namespace ProteinFolding.Tetrahedral

theorem faceSurface_mem_skinSolid (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j) :
    faceSurfaceSite m j a b c hs ∈ skinSolid m j := by
  rw [mem_skinSolid]
  intro i
  rw [tetraCoordinate_faceSurface]
  fin_cases i <;> dsimp <;> constructor <;> omega

theorem faceSurface_mem_skin (m j a b c : ℕ) (hj : 1 ≤ j)
    (hs : a + b + c + 2 = m + 2 * j) : faceSurfaceSite m j a b c hs ∈ skin m j := by
  apply Finset.mem_sdiff.mpr
  refine ⟨faceSurface_mem_skinSolid m j a b c hs, ?_⟩
  intro hp
  have h := ((mem_skinSolid m (j - 1) _).mp hp) 3
  rw [tetraCoordinate_faceSurface] at h
  dsimp at h
  omega

theorem faceSub_mem_skinSolid (m j a b c : ℕ) (hs : a + b + c + 1 = m + 2 * j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : faceSubSite m j a b c hs ∈ skinSolid m j := by
  rw [mem_skinSolid]
  intro i
  rw [tetraCoordinate_faceSub]
  fin_cases i <;> dsimp <;> constructor <;> omega

theorem faceSub_mem_skin (m j a b c : ℕ) (hj : 1 ≤ j)
    (hs : a + b + c + 1 = m + 2 * j) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    faceSubSite m j a b c hs ∈ skin m j := by
  apply Finset.mem_sdiff.mpr
  refine ⟨faceSub_mem_skinSolid m j a b c hs ha hb hc, ?_⟩
  intro hp
  have h := ((mem_skinSolid m (j - 1) _).mp hp) 3
  rw [tetraCoordinate_faceSub] at h
  dsimp at h
  omega

theorem faceSub_step_zero (m j a b c : ℕ) (hs : a + b + c + 1 = m + 2 * j) (ha : 1 ≤ a) :
    step (faceSubSite m j a b c hs) 0 = faceSurfaceSite m j (a - 1) b c (by omega) := by
  apply Subtype.ext
  rw [step_val_of_A _ (faceSubCoordinates_inA m j a b c hs)]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [faceSubSite, faceSurfaceSite, faceSubCoordinates,
    faceSurfaceCoordinates, bondComponent]
  all_goals omega

theorem faceSub_step_one (m j a b c : ℕ) (hs : a + b + c + 1 = m + 2 * j) (hb : 1 ≤ b) :
    step (faceSubSite m j a b c hs) 1 = faceSurfaceSite m j a (b - 1) c (by omega) := by
  apply Subtype.ext
  rw [step_val_of_A _ (faceSubCoordinates_inA m j a b c hs)]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [faceSubSite, faceSurfaceSite, faceSubCoordinates,
    faceSurfaceCoordinates, bondComponent]
  all_goals omega

theorem faceSub_step_two (m j a b c : ℕ) (hs : a + b + c + 1 = m + 2 * j) (hc : 1 ≤ c) :
    step (faceSubSite m j a b c hs) 2 = faceSurfaceSite m j a b (c - 1) (by omega) := by
  apply Subtype.ext
  rw [step_val_of_A _ (faceSubCoordinates_inA m j a b c hs)]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [faceSubSite, faceSurfaceSite, faceSubCoordinates,
    faceSurfaceCoordinates, bondComponent]
  all_goals omega

theorem faceSub_step_three_mem_previousSolid (m j a b c : ℕ) (hj : 1 ≤ j)
    (hs : a + b + c + 1 = m + 2 * j) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    step (faceSubSite m j a b c hs) 3 ∈ skinSolid m (j - 1) := by
  rw [mem_skinSolid]
  intro i
  rw [tetraCoordinate_step_A m (faceSubCoordinates_inA m j a b c hs), tetraCoordinate_faceSub]
  fin_cases i <;> dsimp <;> constructor <;> omega

theorem faceSurface_quadrant (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j) :
    1 ≤ bulkY m (faceSurfaceSite m j a b c hs) ∧
      bulkZ (faceSurfaceSite m j a b c hs) ≤ -2 := by
  dsimp [bulkY, bulkZ, faceSurfaceSite, faceSurfaceCoordinates]
  omega

theorem faceSub_quadrant (m j a b c : ℕ) (hs : a + b + c + 1 = m + 2 * j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ≤ bulkY m (faceSubSite m j a b c hs) ∧ bulkZ (faceSubSite m j a b c hs) ≤ -3 := by
  dsimp [bulkY, bulkZ, faceSubSite, faceSubCoordinates]
  omega

end ProteinFolding.Tetrahedral
