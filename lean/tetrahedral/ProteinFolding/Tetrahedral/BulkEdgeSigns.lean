import ProteinFolding.Tetrahedral.BulkEdgePredicates

/-! Sign and foliation data in translated far-edge boxes. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeAnchor_faces {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ) :
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.k = octRadius m ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.j = -octRadius m ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.a = -octRadius m + 4 * (t : ℤ) ∧
    tetraCoordinate m (bulkEdgeAnchor m F t).val F.b = octRadius m - 4 * (t : ℤ) :=
  (octEdgeZigzag_even hm F t).2

set_option maxHeartbeats 1200000 in
theorem bulkEdgeAnchor_pair_cases (m M t T : ℕ) (F : OctEdgeFrame) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (i j : Fin 4) (hij : i ≠ j) :
    let x := tetraCoordinate m (bulkEdgeAnchor m F t).val i + tetraCoordinate m (bulkEdgeAnchor m F t).val j
    let X := tetraCoordinate M (bulkEdgeAnchor M F T).val i + tetraCoordinate M (bulkEdgeAnchor M F T).val j
    (x = 0 ∧ X = 0) ∨ (x = 4 * (t : ℤ) ∧ X = 4 * (T : ℤ)) ∨
    (x = -4 * (t : ℤ) ∧ X = -4 * (T : ℤ)) ∨
    (x = 2 * octRadius m - 4 * (t : ℤ) ∧ X = 2 * octRadius M - 4 * (T : ℤ)) ∨
    (x = -2 * octRadius m + 4 * (t : ℤ) ∧ X = -2 * octRadius M + 4 * (T : ℤ)) := by
  dsimp only
  obtain ⟨hk, hj, ha, hb⟩ := bulkEdgeAnchor_faces hm F t
  obtain ⟨hK, hJ, hA, hB⟩ := bulkEdgeAnchor_faces hM F T
  rcases F.index_cases i with hi | hi | hi | hi <;>
    rcases F.index_cases j with hj' | hj' | hj' | hj'
  all_goals rw [hi, hj'] at hij ⊢
  all_goals simp_all only []
  all_goals omega

theorem bulkEdgeAnchor_Y_cases (m M t T : ℕ) (F : OctEdgeFrame) (hm : 1 ≤ m) (hM : 1 ≤ M) :
    let y := bulkY m (bulkEdgeAnchor m F t)
    let Y := bulkY M (bulkEdgeAnchor M F T)
    (y = 0 ∧ Y = 0) ∨ (y = 2 * (t : ℤ) ∧ Y = 2 * (T : ℤ)) ∨
    (y = -2 * (t : ℤ) ∧ Y = -2 * (T : ℤ)) ∨
    (y = octRadius m - 2 * (t : ℤ) ∧ Y = octRadius M - 2 * (T : ℤ)) ∨
    (y = -octRadius m + 2 * (t : ℤ) ∧ Y = -octRadius M + 2 * (T : ℤ)) := by
  have h := bulkEdgeAnchor_pair_cases m M t T F hm hM 0 2 (by decide)
  have hy := tetraCoordinate_pair_y m (bulkEdgeAnchor m F t).val
  have hY := tetraCoordinate_pair_y M (bulkEdgeAnchor M F T).val
  change _ = 2 * bulkY m (bulkEdgeAnchor m F t) at hy
  change _ = 2 * bulkY M (bulkEdgeAnchor M F T) at hY
  dsimp only at h ⊢
  omega

theorem bulkEdgeAnchor_z_cases (m M t T : ℕ) (F : OctEdgeFrame) (hm : 1 ≤ m) (hM : 1 ≤ M) :
    let z := (bulkEdgeAnchor m F t).val 2
    let Z := (bulkEdgeAnchor M F T).val 2
    (z = 0 ∧ Z = 0) ∨ (z = 2 * (t : ℤ) ∧ Z = 2 * (T : ℤ)) ∨
    (z = -2 * (t : ℤ) ∧ Z = -2 * (T : ℤ)) ∨
    (z = octRadius m - 2 * (t : ℤ) ∧ Z = octRadius M - 2 * (T : ℤ)) ∨
    (z = -octRadius m + 2 * (t : ℤ) ∧ Z = -octRadius M + 2 * (T : ℤ)) := by
  have h := bulkEdgeAnchor_pair_cases m M t T F hm hM 0 3 (by decide)
  have hz := tetraCoordinate_pair_z m (bulkEdgeAnchor m F t).val
  have hZ := tetraCoordinate_pair_z M (bulkEdgeAnchor M F T).val
  dsimp only at h ⊢
  omega

theorem bulkSign_abs_translate (D : ℕ) (x a X b : ℤ) (hbox : |x - a| ≤ (D : ℤ))
    (htrans : X = x - a + b)
    (hsep : a = b ∨ ((D : ℤ) < a ∧ (D : ℤ) < b) ∨ (a < -(D : ℤ) ∧ b < -(D : ℤ))) :
    bulkSign X = bulkSign x ∧ |X| - |b| = |x| - |a| := by
  have hb := abs_le.mp hbox
  rcases hsep with heq | ⟨ha, hb'⟩ | ⟨ha, hb'⟩
  · have hX : X = x := by omega
    rw [hX, heq]
    exact ⟨rfl, rfl⟩
  · have hx : 0 < x := by omega
    have hX : 0 < X := by omega
    constructor
    · simp only [bulkSign, if_pos hx, if_pos hX]
    · rw [abs_of_nonneg (by omega : 0 ≤ X), abs_of_nonneg (by omega : 0 ≤ b),
        abs_of_nonneg (by omega : 0 ≤ x), abs_of_nonneg (by omega : 0 ≤ a)]
      omega
  · have hx : x < 0 := by omega
    have hX : X < 0 := by omega
    constructor
    · simp only [bulkSign, if_neg (by omega : ¬0 < x), if_neg (by omega : ¬0 < X), if_pos hx, if_pos hX]
    · rw [abs_of_nonpos (by omega : X ≤ 0), abs_of_nonpos (by omega : b ≤ 0),
        abs_of_nonpos (by omega : x ≤ 0), abs_of_nonpos (by omega : a ≤ 0)]
      omega

theorem bulkEdgeReanchor_axis_data (m M t T : ℕ) (F : OctEdgeFrame) (D : ℕ) (p : Site)
    (ht : D + 2 ≤ t) (htm : t + D + 3 ≤ m) (hT : D + 2 ≤ T) (hTM : T + D + 3 ≤ M)
    (hp : InBulkEdgeBox m F t D p) :
    (bulkSign (bulkY M (bulkEdgeReanchor m M t T F p)) = bulkSign (bulkY m p) ∧
      |bulkY M (bulkEdgeReanchor m M t T F p)| - |bulkY M (bulkEdgeAnchor M F T)| =
        |bulkY m p| - |bulkY m (bulkEdgeAnchor m F t)|) ∧
    (bulkSign (bulkZ (bulkEdgeReanchor m M t T F p)) = bulkSign (bulkZ p) ∧
      |bulkZ (bulkEdgeReanchor m M t T F p)| - |bulkZ (bulkEdgeAnchor M F T)| =
        |bulkZ p| - |bulkZ (bulkEdgeAnchor m F t)|) := by
  have hm : 1 ≤ m := by omega
  have hM : 1 ≤ M := by omega
  have hyRaw := hp 1
  have hzRaw := hp 2
  have hty := bulkEdgeReanchor_coordinates m M t T F p 1
  have htz := bulkEdgeReanchor_coordinates m M t T F p 2
  have hybox : |bulkY m p - bulkY m (bulkEdgeAnchor m F t)| ≤ (D : ℤ) := by
    have heq : bulkY m p - bulkY m (bulkEdgeAnchor m F t) = p.val 1 - (bulkEdgeAnchor m F t).val 1 := by
      unfold bulkY
      omega
    rwa [heq]
  have hzbox : |bulkZ p - bulkZ (bulkEdgeAnchor m F t)| ≤ (D : ℤ) := by
    have heq : bulkZ p - bulkZ (bulkEdgeAnchor m F t) = p.val 2 - (bulkEdgeAnchor m F t).val 2 := by
      unfold bulkZ
      omega
    rwa [heq]
  have hytrans : bulkY M (bulkEdgeReanchor m M t T F p) = bulkY m p - bulkY m (bulkEdgeAnchor m F t) +
      bulkY M (bulkEdgeAnchor M F T) := by unfold bulkY; omega
  have hztrans : bulkZ (bulkEdgeReanchor m M t T F p) = bulkZ p - bulkZ (bulkEdgeAnchor m F t) +
      bulkZ (bulkEdgeAnchor M F T) := by unfold bulkZ; omega
  constructor
  · apply bulkSign_abs_translate D _ _ _ _ hybox hytrans
    have hc := bulkEdgeAnchor_Y_cases m M t T F hm hM
    dsimp only at hc
    dsimp [octRadius] at hc
    omega
  · apply bulkSign_abs_translate D _ _ _ _ hzbox hztrans
    have hc := bulkEdgeAnchor_z_cases m M t T F hm hM
    have hz0 : bulkZ (bulkEdgeAnchor m F t) = (bulkEdgeAnchor m F t).val 2 - 1 := rfl
    have hZ0 : bulkZ (bulkEdgeAnchor M F T) = (bulkEdgeAnchor M F T).val 2 - 1 := rfl
    dsimp only at hc
    dsimp [octRadius] at hc
    omega

end ProteinFolding.Tetrahedral
