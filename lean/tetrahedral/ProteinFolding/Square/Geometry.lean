import ProteinFolding.Square.Statement

/-! The four direction indices enumerate the neighbours bijectively. -/

namespace ProteinFolding.Square

theorem latticeDistance_eq (p q : Site) :
    latticeDistance p q = (p 0 - q 0).natAbs + (p 1 - q 1).natAbs := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp [latticeDistance, hu]

theorem site_ext {p q : Site} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  funext k
  match k with
  | 0 => exact h₀
  | 1 => exact h₁

theorem step_adj (p : Site) (d : Fin 4) : squareLattice.Adj p (step p d) := by
  change latticeDistance p (step p d) = 1
  rw [latticeDistance_eq]
  match d with
  | 0 => simp [step]
  | 1 => simp [step]
  | 2 => simp [step]
  | 3 => simp [step]

theorem step_inj (p : Site) : Function.Injective (step p) := by
  intro d e h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  match d, e with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => rfl
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 2 | 1, 3 |
    2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
    simp [step] at h₀ h₁ <;> omega

theorem adj_step {p q : Site} (h : squareLattice.Adj p q) :
    ∃ d : Fin 4, step p d = q := by
  change latticeDistance p q = 1 at h
  rw [latticeDistance_eq] at h
  have ha : p 0 - q 0 = 0 ∨ p 0 - q 0 = 1 ∨ p 0 - q 0 = -1 := by omega
  have hb : p 1 - q 1 = 0 ∨ p 1 - q 1 = 1 ∨ p 1 - q 1 = -1 := by omega
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · simp [ha, hb] at h
    · exact ⟨3, site_ext (by simp [step]; omega) (by simp [step]; omega)⟩
    · exact ⟨2, site_ext (by simp [step]; omega) (by simp [step]; omega)⟩
  · have hb : p 1 = q 1 := by simp [ha] at h; omega
    exact ⟨1, site_ext (by simp [step]; omega) (by simp [step]; omega)⟩
  · have hb : p 1 = q 1 := by simp [ha] at h; omega
    exact ⟨0, site_ext (by simp [step]; omega) (by simp [step]; omega)⟩

theorem adj_iff_step (p q : Site) :
    squareLattice.Adj p q ↔ ∃ d : Fin 4, step p d = q :=
  ⟨adj_step, by rintro ⟨d, rfl⟩; exact step_adj p d⟩

end ProteinFolding.Square
