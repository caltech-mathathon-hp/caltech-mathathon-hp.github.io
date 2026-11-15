import ProteinFolding.Tetrahedral.BulkLineCoordinates

/-! Alpha is constant on every foliation line, and its bend is unique. -/

namespace ProteinFolding.Tetrahedral

theorem abs_unit_adjacent (x y : ℤ) (h : y = x + 1 ∨ y = x - 1) :
    |y| = |x| + 1 ∨ |y| = |x| - 1 := by
  rcases h with rfl | rfl
  · by_cases hx : 0 ≤ x
    · left
      rw [abs_of_nonneg hx, abs_of_nonneg (by omega : 0 ≤ x + 1)]
    · right
      rw [abs_of_nonpos (by omega : x ≤ 0), abs_of_nonpos (by omega : x + 1 ≤ 0)]
      omega
  · by_cases hx : x ≤ 0
    · left
      rw [abs_of_nonpos hx, abs_of_nonpos (by omega : x - 1 ≤ 0)]
      omega
    · right
      rw [abs_of_nonneg (by omega : 0 ≤ x), abs_of_nonneg (by omega : 0 ≤ x - 1)]

theorem bulkRungGraph_adj_rho_alpha (m : ℕ) {p q : Site}
    (h : (bulkRungGraph m).Adj p q) :
    (bulkRho m q = bulkRho m p + 2 ∨ bulkRho m q = bulkRho m p - 2) ∧
      bulkAlpha m q = bulkAlpha m p := by
  have hd := bulk_adj_deltas m h.1
  have hy : bulkY m q = bulkY m p + 1 ∨ bulkY m q = bulkY m p - 1 := by omega
  have hz : bulkZ q = bulkZ p + 1 ∨ bulkZ q = bulkZ p - 1 := by omega
  have hay := abs_unit_adjacent (bulkY m p) (bulkY m q) hy
  have haz := abs_unit_adjacent (bulkZ p) (bulkZ q) hz
  have hne := h.2
  dsimp [bulkRho, bulkAlpha] at hne ⊢
  constructor <;> omega

theorem bulkWalk_alpha (m : ℕ) {p q : Site} (w : (bulkRungGraph m).Walk p q) :
    bulkAlpha m q = bulkAlpha m p := by
  induction w with
  | nil => rfl
  | @cons p r q hadj w ih => exact ih.trans (bulkRungGraph_adj_rho_alpha m hadj).2

theorem bulkRho_ge_abs_alpha (m : ℕ) (p : Site) : |bulkAlpha m p| ≤ bulkRho m p := by
  have hy := abs_nonneg (bulkY m p)
  have hz := abs_nonneg (bulkZ p)
  unfold bulkRho bulkAlpha
  apply abs_le.mpr
  constructor <;> omega

theorem bulk_bend_iff_rho_eq_abs_alpha (m : ℕ) (p : Site) :
    (bulkY m p = 0 ∨ bulkZ p = 0) ↔ bulkRho m p = |bulkAlpha m p| := by
  have hy := abs_nonneg (bulkY m p)
  have hz := abs_nonneg (bulkZ p)
  constructor
  · rintro (hy0 | hz0)
    · simp only [bulkRho, bulkAlpha, hy0, abs_zero, zero_add, zero_sub, abs_neg, abs_abs]
    · simp only [bulkRho, bulkAlpha, hz0, abs_zero, add_zero, sub_zero, abs_abs]
  · intro heq
    unfold bulkRho bulkAlpha at heq
    have hnum : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → a + b = |a - b| → a = 0 ∨ b = 0 := by
      intro a b ha hb he
      by_cases hab : a ≤ b
      · rw [abs_of_nonpos (by omega : a - b ≤ 0)] at he
        left
        omega
      · rw [abs_of_nonneg (by omega : 0 ≤ a - b)] at he
        right
        omega
    rcases hnum _ _ hy hz heq with h | h
    · exact Or.inl (abs_eq_zero.mp h)
    · exact Or.inr (abs_eq_zero.mp h)

theorem bulk_bend_neighbour_up (m : ℕ) {p q : Site}
    (hp : bulkY m p = 0 ∨ bulkZ p = 0) (h : (bulkRungGraph m).Adj p q) :
    bulkRho m q = bulkRho m p + 2 := by
  have hpmin := (bulk_bend_iff_rho_eq_abs_alpha m p).mp hp
  have hqmin := bulkRho_ge_abs_alpha m q
  have hstep := bulkRungGraph_adj_rho_alpha m h
  rw [hstep.2] at hqmin
  omega

/-- Two distinct bends cannot be connected by a rung path. -/
theorem bulk_bend_unique_of_reachable (m : ℕ) {p q : Site}
    (hp : bulkY m p = 0 ∨ bulkZ p = 0) (hq : bulkY m q = 0 ∨ bulkZ q = 0)
    (hreach : (bulkRungGraph m).Reachable p q) : p = q := by
  by_contra hpq
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hlen : 0 < w.length := by
    by_contra he
    have heq : w.length = 0 := by omega
    have h0 := w.getVert_length
    have hs := w.getVert_zero
    rw [heq, hs] at h0
    exact hpq h0
  have hfirst := w.adj_getVert_succ (show 0 < w.length from hlen)
  rw [w.getVert_zero] at hfirst
  have hfirstup := bulk_bend_neighbour_up m hp hfirst
  change bulkRho m (w.getVert 1) = bulkRho m p + 2 at hfirstup
  have halpha := bulkWalk_alpha m w
  have hpmin := (bulk_bend_iff_rho_eq_abs_alpha m p).mp hp
  have hqmin := (bulk_bend_iff_rho_eq_abs_alpha m q).mp hq
  have hends : bulkRho m q = bulkRho m p := by rw [hqmin, halpha, ← hpmin]
  have hne : (Finset.range (w.length + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range (w.length + 1))
    (fun i => bulkRho m (w.getVert i)) hne
  have hib : i ≤ w.length := by have := Finset.mem_range.mp hi; omega
  have hfirstle := hmax 1 (Finset.mem_range.mpr (by omega))
  have hipos : 0 < i := by
    by_contra he
    have hi0 : i = 0 := by omega
    rw [hi0, w.getVert_zero] at hfirstle
    omega
  have hilt : i < w.length := by
    by_contra he
    have hil : i = w.length := by omega
    rw [hil, w.getVert_length, hends] at hfirstle
    omega
  have hleft := w.adj_getVert_succ (show i - 1 < w.length by omega)
  have hidx : i - 1 + 1 = i := by omega
  rw [hidx] at hleft
  have hright := w.adj_getVert_succ hilt
  have heq : w.getVert (i - 1) = w.getVert (i + 1) :=
    bulk_lower_rung_unique m (w.getVert i)
      ((bulkRungGraph_adj_iff m _ _).mp hleft.symm)
      ((bulkRungGraph_adj_iff m _ _).mp hright)
      (hmax (i - 1) (Finset.mem_range.mpr (by omega)))
      (hmax (i + 1) (Finset.mem_range.mpr (by omega)))
  have hbad := hw.getVert_injOn (show i - 1 ≤ w.length by omega)
    (show i + 1 ≤ w.length by omega) heq
  omega

theorem bulk_component_unique_bend (m : ℕ) (p : Site) :
    ∃! b : Site, (bulkRungGraph m).Reachable p b ∧ (bulkY m b = 0 ∨ bulkZ b = 0) := by
  refine ⟨bulkBendPoint m p, ⟨bulkBendPoint_reachable m p, bulkBendPoint_is_bend m p⟩, ?_⟩
  intro b hb
  exact bulk_bend_unique_of_reachable m hb.2 (bulkBendPoint_is_bend m p)
    (hb.1.symm.trans (bulkBendPoint_reachable m p))

end ProteinFolding.Tetrahedral
