import ProteinFolding.Tetrahedral.BulkVertexLocality

/-! The sign and foliation data also translate uniformly inside vertex boxes. -/

namespace ProteinFolding.Tetrahedral

def bulkVertexYExpansion (m n : ℕ) (v : Fin 6) : ℤ :=
  match v.val with
  | 1 => 2 * ((n : ℤ) - m)
  | 4 => 2 * ((n : ℤ) - m)
  | _ => 0

def bulkVertexZExpansion (m n : ℕ) (v : Fin 6) : ℤ :=
  match v.val with
  | 2 => 2 * ((n : ℤ) - m)
  | 3 => 2 * ((n : ℤ) - m)
  | _ => 0

set_option maxHeartbeats 1200000 in
theorem bulkReanchor_absY (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    |bulkY n (bulkReanchorSite m n v p)| = |bulkY m p| + bulkVertexYExpansion m n v := by
  have hb := abs_le.mp (hp 1)
  have ht := bulkReanchorSite_coordinates m n v p 1
  fin_cases v
  all_goals dsimp [bulkY, bulkVertexYExpansion, bulkPatchVertex, octVertexSite,
    octVertexCoordinates, octCentre, octRadius] at hb ht ⊢
  all_goals try simp only [add_zero]
  all_goals first
    | (congr 1; omega)
    | (rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega)
    | (rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega)

set_option maxHeartbeats 1200000 in
theorem bulkReanchor_absZ (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    |bulkZ (bulkReanchorSite m n v p)| = |bulkZ p| + bulkVertexZExpansion m n v := by
  have hb := abs_le.mp (hp 2)
  have ht := bulkReanchorSite_coordinates m n v p 2
  fin_cases v
  all_goals dsimp [bulkZ, bulkVertexZExpansion, bulkPatchVertex, octVertexSite,
    octVertexCoordinates, octCentre, octRadius] at hb ht ⊢
  all_goals try simp only [add_zero]
  all_goals first
    | (congr 1; omega)
    | (rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega)
    | (rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega)

theorem bulkReanchor_rho_alpha (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkRho n (bulkReanchorSite m n v p) = bulkRho m p +
      bulkVertexYExpansion m n v + bulkVertexZExpansion m n v ∧
    bulkAlpha n (bulkReanchorSite m n v p) = bulkAlpha m p +
      bulkVertexYExpansion m n v - bulkVertexZExpansion m n v := by
  have hy := bulkReanchor_absY m n v D p hm hn hp
  have hz := bulkReanchor_absZ m n v D p hm hn hp
  unfold bulkRho bulkAlpha
  rw [hy, hz]
  constructor <;> ring

set_option maxHeartbeats 1200000 in
theorem bulkReanchor_signs (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkSign (bulkY n (bulkReanchorSite m n v p)) = bulkSign (bulkY m p) ∧
      bulkSign (bulkZ (bulkReanchorSite m n v p)) = bulkSign (bulkZ p) := by
  have hby := abs_le.mp (hp 1)
  have hbz := abs_le.mp (hp 2)
  have hty := bulkReanchorSite_coordinates m n v p 1
  have htz := bulkReanchorSite_coordinates m n v p 2
  constructor
  · fin_cases v
    all_goals dsimp [bulkY, bulkPatchVertex, octVertexSite, octVertexCoordinates,
      octCentre, octRadius] at hby hty ⊢
    all_goals unfold bulkSign
    all_goals split_ifs <;> omega
  · fin_cases v
    all_goals dsimp [bulkZ, bulkPatchVertex, octVertexSite, octVertexCoordinates,
      octCentre, octRadius] at hbz htz ⊢
    all_goals unfold bulkSign
    all_goals split_ifs <;> omega

theorem bulkSign_eq_zero_iff (x : ℤ) : bulkSign x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · subst x
    decide
  · exact iff_of_false (by have h := bulkSign_unit_of_ne x hx; omega) hx

theorem bulkReanchor_zeros (m n : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    (bulkY n (bulkReanchorSite m n v p) = 0 ↔ bulkY m p = 0) ∧
      (bulkZ (bulkReanchorSite m n v p) = 0 ↔ bulkZ p = 0) := by
  have hs := bulkReanchor_signs m n v D p hm hn hp
  constructor
  · rw [← bulkSign_eq_zero_iff, hs.1, bulkSign_eq_zero_iff]
  · rw [← bulkSign_eq_zero_iff, hs.2, bulkSign_eq_zero_iff]

theorem bulkReanchor_yz_differences (m n : ℕ) (v : Fin 6) (p q : Site) :
    bulkY n (bulkReanchorSite m n v q) - bulkY n (bulkReanchorSite m n v p) =
      bulkY m q - bulkY m p ∧
    bulkZ (bulkReanchorSite m n v q) - bulkZ (bulkReanchorSite m n v p) = bulkZ q - bulkZ p := by
  have hp1 := bulkReanchorSite_coordinates m n v p 1
  have hq1 := bulkReanchorSite_coordinates m n v q 1
  have hp2 := bulkReanchorSite_coordinates m n v p 2
  have hq2 := bulkReanchorSite_coordinates m n v q 2
  unfold bulkY bulkZ
  constructor <;> omega

theorem bulkReanchor_rule_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n) (hp : InBulkVertexBox m v D p) :
    bulkRuleNeighbour n (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔
      bulkRuleNeighbour m p q := by
  have hsign := bulkReanchor_signs m n v D p hm hn hp
  have hzero := bulkReanchor_zeros m n v D p hm hn hp
  have hdiff := bulkReanchor_yz_differences m n v p q
  unfold bulkRuleNeighbour
  rw [bulkReanchorSite_adj_iff, hsign.1, hsign.2, hdiff.1, hdiff.2]
  simp only [ne_eq, hzero.1, hzero.2]

theorem bulkReanchor_rung_iff (m n : ℕ) (v : Fin 6) (D : ℕ) (p q : Site)
    (hm : D + 2 ≤ m) (hn : D + 2 ≤ n)
    (hp : InBulkVertexBox m v D p) (hq : InBulkVertexBox m v D q) :
    (bulkRungGraph n).Adj (bulkReanchorSite m n v p) (bulkReanchorSite m n v q) ↔
      (bulkRungGraph m).Adj p q := by
  have hρp := (bulkReanchor_rho_alpha m n v D p hm hn hp).1
  have hρq := (bulkReanchor_rho_alpha m n v D q hm hn hq).1
  change (_ ∧ _ ≠ _) ↔ (_ ∧ _ ≠ _)
  rw [bulkReanchorSite_adj_iff]
  exact and_congr_right (fun _ => by rw [hρp, hρq]; omega)

end ProteinFolding.Tetrahedral
