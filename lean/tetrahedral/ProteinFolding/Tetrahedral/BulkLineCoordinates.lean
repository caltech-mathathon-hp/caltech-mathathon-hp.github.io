import ProteinFolding.Tetrahedral.BulkLines

/-! Every site reaches a bend by an explicit finite, strictly descending rung path. -/

namespace ProteinFolding.Tetrahedral

theorem bulkArmPoint_inward_distances (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site)
    (hy : 0 ≤ sy * bulkY m p) (hz : 0 ≤ sz * bulkZ p) (n : ℕ)
    (hny : (n : ℤ) ≤ |bulkY m p|) (hnz : (n : ℤ) ≤ |bulkZ p|) :
    |bulkY m (bulkArmPoint (-sy) (-sz) p n)| = |bulkY m p| - n ∧
      |bulkZ (bulkArmPoint (-sy) (-sz) p n)| = |bulkZ p| - n := by
  have hnsy : -sy = 1 ∨ -sy = -1 := by omega
  have hnsz : -sz = 1 ∨ -sz = -1 := by omega
  have hyN : sy * bulkY m (bulkArmPoint (-sy) (-sz) p n) = sy * bulkY m p - n := by
    rw [bulkArmPoint_y m (-sy) (-sz) hnsy hnsz]
    rcases hsy with rfl | rfl <;> ring
  have hzN : sz * bulkZ (bulkArmPoint (-sy) (-sz) p n) = sz * bulkZ p - n := by
    rw [bulkArmPoint_z (-sy) (-sz) hnsy hnsz]
    rcases hsz with rfl | rfl <;> ring
  have hyabs := abs_eq_unit_mul sy (bulkY m p) hsy hy
  have hzabs := abs_eq_unit_mul sz (bulkZ p) hsz hz
  rw [abs_eq_unit_mul sy (bulkY m (bulkArmPoint (-sy) (-sz) p n)) hsy (by omega),
    abs_eq_unit_mul sz (bulkZ (bulkArmPoint (-sy) (-sz) p n)) hsz (by omega), hyabs, hzabs]
  exact ⟨hyN, hzN⟩

theorem bulkArmPoint_inward_rho_alpha (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site)
    (hy : 0 ≤ sy * bulkY m p) (hz : 0 ≤ sz * bulkZ p) (n : ℕ)
    (hny : (n : ℤ) ≤ |bulkY m p|) (hnz : (n : ℤ) ≤ |bulkZ p|) :
    bulkRho m (bulkArmPoint (-sy) (-sz) p n) = bulkRho m p - 2 * n ∧
      bulkAlpha m (bulkArmPoint (-sy) (-sz) p n) = bulkAlpha m p := by
  have h := bulkArmPoint_inward_distances m sy sz hsy hsz p hy hz n hny hnz
  dsimp [bulkRho, bulkAlpha]
  rw [h.1, h.2]
  constructor <;> omega

def bulkYSign (m : ℕ) (p : Site) : ℤ := if 0 ≤ bulkY m p then 1 else -1
def bulkZSign (p : Site) : ℤ := if 0 ≤ bulkZ p then 1 else -1
def bulkBendDistance (m : ℕ) (p : Site) : ℕ := (min |bulkY m p| |bulkZ p|).toNat

theorem bulkYSign_unit (m : ℕ) (p : Site) : bulkYSign m p = 1 ∨ bulkYSign m p = -1 := by
  unfold bulkYSign
  split_ifs <;> omega

theorem bulkZSign_unit (p : Site) : bulkZSign p = 1 ∨ bulkZSign p = -1 := by
  unfold bulkZSign
  split_ifs <;> omega

theorem bulkYSign_nonneg (m : ℕ) (p : Site) : 0 ≤ bulkYSign m p * bulkY m p := by
  unfold bulkYSign
  split_ifs <;> omega

theorem bulkZSign_nonneg (p : Site) : 0 ≤ bulkZSign p * bulkZ p := by
  unfold bulkZSign
  split_ifs <;> omega

theorem bulkBendDistance_eq (m : ℕ) (p : Site) :
    (bulkBendDistance m p : ℤ) = min |bulkY m p| |bulkZ p| := by
  have hy := abs_nonneg (bulkY m p)
  have hz := abs_nonneg (bulkZ p)
  dsimp [bulkBendDistance]
  omega

def bulkInwardPoint (m : ℕ) (p : Site) (n : ℕ) : Site :=
  bulkArmPoint (-bulkYSign m p) (-bulkZSign p) p n

def bulkBendPoint (m : ℕ) (p : Site) : Site := bulkInwardPoint m p (bulkBendDistance m p)

theorem bulkInwardPoint_rho_alpha (m : ℕ) (p : Site) (n : ℕ)
    (hn : n ≤ bulkBendDistance m p) :
    bulkRho m (bulkInwardPoint m p n) = bulkRho m p - 2 * n ∧
      bulkAlpha m (bulkInwardPoint m p n) = bulkAlpha m p := by
  have hdist := bulkBendDistance_eq m p
  apply bulkArmPoint_inward_rho_alpha m (bulkYSign m p) (bulkZSign p)
    (bulkYSign_unit m p) (bulkZSign_unit p) p (bulkYSign_nonneg m p) (bulkZSign_nonneg p)
  · have h := min_le_left |bulkY m p| |bulkZ p|
    omega
  · have h := min_le_right |bulkY m p| |bulkZ p|
    omega

theorem bulkBendPoint_is_bend (m : ℕ) (p : Site) :
    bulkY m (bulkBendPoint m p) = 0 ∨ bulkZ (bulkBendPoint m p) = 0 := by
  have hdist := bulkBendDistance_eq m p
  have h := bulkArmPoint_inward_distances m (bulkYSign m p) (bulkZSign p)
    (bulkYSign_unit m p) (bulkZSign_unit p) p (bulkYSign_nonneg m p) (bulkZSign_nonneg p)
    (bulkBendDistance m p) (by rw [hdist]; exact min_le_left _ _)
    (by rw [hdist]; exact min_le_right _ _)
  change |bulkY m (bulkBendPoint m p)| = _ ∧ |bulkZ (bulkBendPoint m p)| = _ at h
  rcases le_total |bulkY m p| |bulkZ p| with hle | hle
  · left
    rw [min_eq_left hle] at hdist
    have hz : |bulkY m (bulkBendPoint m p)| = 0 := by omega
    exact abs_eq_zero.mp hz
  · right
    rw [min_eq_right hle] at hdist
    have hz : |bulkZ (bulkBendPoint m p)| = 0 := by omega
    exact abs_eq_zero.mp hz

theorem bulkInwardPoint_adj (m : ℕ) (p : Site) (n : ℕ)
    (hn : n < bulkBendDistance m p) :
    (bulkRungGraph m).Adj (bulkInwardPoint m p n) (bulkInwardPoint m p (n + 1)) := by
  have h0 := (bulkInwardPoint_rho_alpha m p n (by omega)).1
  have h1 := (bulkInwardPoint_rho_alpha m p (n + 1) (by omega)).1
  refine ⟨bulkArmPoint_adj _ _ p n, ?_⟩
  push_cast at h1
  omega

def bulkInwardWalk (m : ℕ) (p : Site) (n : ℕ) (hn : n ≤ bulkBendDistance m p) :
    (bulkRungGraph m).Walk p (bulkInwardPoint m p n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact (ih (by omega)).concat (bulkInwardPoint_adj m p n (by omega))

/-- Every site lies in the component of an explicitly computed bend. -/
theorem bulkBendPoint_reachable (m : ℕ) (p : Site) :
    (bulkRungGraph m).Reachable p (bulkBendPoint m p) :=
  ⟨bulkInwardWalk m p (bulkBendDistance m p) (le_refl _)⟩

end ProteinFolding.Tetrahedral
