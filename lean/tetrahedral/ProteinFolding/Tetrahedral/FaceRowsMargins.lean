import ProteinFolding.Tetrahedral.FaceRowsColumnOwners

/-! Complete column intersections with F' bilayers and their margins. -/

namespace ProteinFolding.Tetrahedral

def OnDanglingColumn (m : ℕ) (p : Site) : Prop :=
  ∃ C : DanglingColumn m, ∃ n : ℕ, C.point n = p

theorem faceSurface_column_coordinates {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 2 = m + 2 * j)
    (heq : C.point n = faceSurfaceSite m j a b c hs) :
    ∃ a₀ b₀ c₀ : ℕ, ∃ hs₀ : a₀ + b₀ + c₀ + 2 = m,
      C = faceDanglingColumn m a₀ b₀ c₀ hs₀ ∧ n = 2 * j - 1 ∧
      a = a₀ + j ∧ b = b₀ + j ∧ c = c₀ := by
  have howner := column_surface_owner C hj hs heq
  obtain ⟨a₀, b₀, c₀, hs₀, hC⟩ := column_over_face_coordinates C howner.1 howner.2
  have hskin : C.point n ∈ skin m j := by rw [heq]; exact faceSurface_mem_skin m j a b c hj hs
  have hn := (C.point_mem_skin_iff_two_indices n j hj).mp hskin
  rw [hC] at heq
  rcases hn with hn | hn
  · rw [hn, faceDanglingColumn_sub_in_skin m a₀ b₀ c₀ hs₀ j hj] at heq
    have hx := congrArg (fun p : Site => p.val 0) heq
    dsimp [faceSubSite, faceSubCoordinates, faceSurfaceSite, faceSurfaceCoordinates] at hx
    omega
  · rw [hn, faceDanglingColumn_surface_in_skin m a₀ b₀ c₀ hs₀ j hj] at heq
    have hp := faceSurfaceSite_injective m j _ _ heq
    exact ⟨a₀, b₀, c₀, hs₀, hC, hn, hp.1.symm, hp.2.1.symm, hp.2.2.symm⟩

theorem faceSub_column_coordinates {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 1 = m + 2 * j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (heq : C.point n = faceSubSite m j a b c hs) :
    ∃ a₀ b₀ c₀ : ℕ, ∃ hs₀ : a₀ + b₀ + c₀ + 2 = m,
      C = faceDanglingColumn m a₀ b₀ c₀ hs₀ ∧ n = 2 * j - 2 ∧
      a = a₀ + j ∧ b = b₀ + j ∧ c = c₀ + 1 := by
  have howner := column_sub_owner C hj hs ha hb hc heq
  obtain ⟨a₀, b₀, c₀, hs₀, hC⟩ := column_over_face_coordinates C howner.1 howner.2
  have hskin : C.point n ∈ skin m j := by rw [heq]; exact faceSub_mem_skin m j a b c hj hs ha hb hc
  have hn := (C.point_mem_skin_iff_two_indices n j hj).mp hskin
  rw [hC] at heq
  rcases hn with hn | hn
  · rw [hn, faceDanglingColumn_sub_in_skin m a₀ b₀ c₀ hs₀ j hj] at heq
    have hp := faceSubSite_injective m j _ _ heq
    exact ⟨a₀, b₀, c₀, hs₀, hC, hn, hp.1.symm, hp.2.1.symm, hp.2.2.symm⟩
  · rw [hn, faceDanglingColumn_surface_in_skin m a₀ b₀ c₀ hs₀ j hj] at heq
    have hx := congrArg (fun p : Site => p.val 0) heq
    dsimp [faceSubSite, faceSubCoordinates, faceSurfaceSite, faceSurfaceCoordinates] at hx
    omega

theorem faceSurface_column_margin {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 2 = m + 2 * j)
    (heq : C.point n = faceSurfaceSite m j a b c hs) : j ≤ a ∧ j ≤ b := by
  obtain ⟨a₀, b₀, c₀, hs₀, _, _, ha, hb, _⟩ := faceSurface_column_coordinates C hj hs heq
  omega

theorem faceSub_column_margin {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 1 = m + 2 * j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (heq : C.point n = faceSubSite m j a b c hs) : j ≤ a ∧ j ≤ b := by
  obtain ⟨a₀, b₀, c₀, hs₀, _, _, ha', hb', _⟩ := faceSub_column_coordinates C hj hs ha hb hc heq
  omega

theorem faceSurface_not_on_column_of_a_lt {m j a b c : ℕ} (hj : 1 ≤ j)
    (hs : a + b + c + 2 = m + 2 * j) (ha : a < j) :
    ¬ OnDanglingColumn m (faceSurfaceSite m j a b c hs) := by
  rintro ⟨C, n, heq⟩
  have h := (faceSurface_column_margin C hj hs heq).1
  omega

theorem faceSurface_not_on_column_of_b_lt {m j a b c : ℕ} (hj : 1 ≤ j)
    (hs : a + b + c + 2 = m + 2 * j) (hb : b < j) :
    ¬ OnDanglingColumn m (faceSurfaceSite m j a b c hs) := by
  rintro ⟨C, n, heq⟩
  have h := (faceSurface_column_margin C hj hs heq).2
  omega

theorem faceSub_not_on_column_of_a_lt {m j a b c : ℕ} (hj : 1 ≤ j)
    (hs : a + b + c + 1 = m + 2 * j) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (haj : a < j) :
    ¬ OnDanglingColumn m (faceSubSite m j a b c hs) := by
  rintro ⟨C, n, heq⟩
  have h := (faceSub_column_margin C hj hs ha hb hc heq).1
  omega

theorem faceSub_not_on_column_of_b_lt {m j a b c : ℕ} (hj : 1 ≤ j)
    (hs : a + b + c + 1 = m + 2 * j) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hbj : b < j) :
    ¬ OnDanglingColumn m (faceSubSite m j a b c hs) := by
  rintro ⟨C, n, heq⟩
  have h := (faceSub_column_margin C hj hs ha hb hc heq).2
  omega

end ProteinFolding.Tetrahedral
