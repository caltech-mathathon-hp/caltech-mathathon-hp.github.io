import ProteinFolding.Tetrahedral.NearFieldBorrowedColumns

/-! Skin rank and upper endpoint of the actual borrowed column prefix. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem borrowedPoint_mem_skin (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (n : ℕ) : borrowedPoint m a b c hs ha n ∈ skin m (n / 2 + 1) := by
  cases n with
  | zero => exact (faceDanglingColumn m a b c hs).point_mem_skin 0
  | succ n => exact (faceDanglingColumn m (a - 1) b (c + 1) (by omega)).point_mem_skin (n + 1)

theorem borrowedPrefix_mem_solid (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (j : ℕ) (hj : 1 ≤ j) (i : Fin (2 * j - 1)) :
    (borrowedPrefixFold m a b c hs ha (2 * j - 1)).pos i ∈ skinSolid m j := by
  have hskin := borrowedPoint_mem_skin m a b c hs ha i.val
  have hrank : i.val / 2 + 1 ≤ j := by have hi := i.isLt; omega
  exact skinSolid_mono m hrank (skin_subset_solid m _ hskin)

theorem borrowedPrefix_first (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (j : ℕ) (i : Fin (2 * j - 1)) (hi : i.val = 0) :
    (borrowedPrefixFold m a b c hs ha (2 * j - 1)).pos i =
      (faceDanglingColumn m a b c hs).seed := by
  change borrowedPoint m a b c hs ha i.val = _
  rw [hi, borrowedPoint]

theorem borrowedPoint_at_skin_top (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (j : ℕ) (hj : 2 ≤ j) :
    borrowedPoint m a b c hs ha (2 * j - 2) =
      faceSubSite m j (a - 1 + j) (b + j) (c + 2) (by omega) := by
  rw [show 2 * j - 2 = (2 * j - 3) + 1 by omega, borrowedPoint]
  rw [show 2 * j - 3 + 1 = 2 * j - 2 by omega]
  exact faceDanglingColumn_sub_in_skin m (a - 1) b (c + 1) (by omega) j (by omega)

theorem borrowedPrefix_last (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (j : ℕ) (hj : 2 ≤ j) (i : Fin (2 * j - 1))
    (hi : i.val + 1 = 2 * j - 1) :
    (borrowedPrefixFold m a b c hs ha (2 * j - 1)).pos i =
      faceSubSite m j (a - 1 + j) (b + j) (c + 2) (by omega) := by
  change borrowedPoint m a b c hs ha i.val = _
  rw [show i.val = 2 * j - 2 by omega]
  exact borrowedPoint_at_skin_top m a b c hs ha j hj

end ProteinFolding.Tetrahedral.NearField
