import ProteinFolding.Tetrahedral.NearFieldTetherRows
import ProteinFolding.Tetrahedral.NearFieldBorrowedSkins
import ProteinFolding.Tetrahedral.NearFieldColumnPieces

/-! Separation of the actual entry corner from its borrowed source column
and its separator column. This is proved by coordinates on the c=1 row
and by the b=j-1 column-free margin on the second row. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem borrowedPoint_on_column (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (n : ℕ) : OnDanglingColumn m (borrowedPoint m a b c hs ha n) := by
  cases n with
  | zero => exact ⟨faceDanglingColumn m a b c hs, 0, rfl⟩
  | succ n => exact ⟨faceDanglingColumn m (a - 1) b (c + 1) (by omega), n + 1, rfl⟩

theorem borrowedPoint_ne_entryRowC (m a b j n r : ℕ)
    (hs : a + b + 0 + 2 = m) (ha : 1 ≤ a) (hj : 2 ≤ j) (hn : n < 2 * j - 1) :
    borrowedPoint m a b 0 hs ha n ≠
      faceRowPoint 2 m j (a - 1 + j) (b + j) 1 (by omega) r := by
  intro heq
  have hz := congrArg (fun q : Site => q.val 2) heq
  cases n with
  | zero =>
    dsimp only [borrowedPoint] at hz
    rw [faceDanglingColumn_seed] at hz
    dsimp [faceSubSite, faceSubCoordinates, faceRowPoint, faceRowCoordinates] at hz
    omega
  | succ n =>
    dsimp only [borrowedPoint] at hz
    rw [faceDanglingColumn_point_coordinates] at hz
    dsimp [faceRowPoint, faceRowCoordinates] at hz
    omega

theorem borrowedPoint_ne_farColumn (m a b c d e n r : ℕ)
    (hs : a + b + 0 + 2 = m) (ht : c + d + e + 2 = m) (ha : 1 ≤ a) (he : 2 ≤ e) :
    borrowedPoint m a b 0 hs ha n ≠ (faceDanglingColumn m c d e ht).point r := by
  intro heq
  have hx := congrArg (fun q : Site => q.val 0) heq
  cases n with
  | zero =>
    dsimp only [borrowedPoint] at hx
    rw [faceColumn_seed_x, faceDanglingColumn_point_coordinates] at hx
    omega
  | succ n =>
    dsimp only [borrowedPoint] at hx
    rw [faceDanglingColumn_point_coordinates, faceDanglingColumn_point_coordinates] at hx
    omega

theorem entryRowC_ne_farColumn (m j a b c d e r n : ℕ)
    (hs : a + b + 1 + 2 = m + 2 * j) (ht : c + d + e + 2 = m) (he : 2 ≤ e) :
    faceRowPoint 2 m j a b 1 hs r ≠ (faceDanglingColumn m c d e ht).point n := by
  intro heq
  have hx := congrArg (fun q : Site => q.val 0) heq
  dsimp only at hx
  rw [faceDanglingColumn_point_coordinates] at hx
  dsimp [faceRowPoint, faceRowCoordinates] at hx
  omega

def entryAnchorA (p : ConstructionParameters) (k : ℕ) : ℕ := p.side - 2 - 3 * (k + 1)

theorem entryAnchor_equation (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    entryAnchorA p k + 3 * (k + 1) + 0 + 2 = p.side := by
  have h := p.entry_column_triangle_room k hk
  unfold entryAnchorA
  omega

theorem entryAnchor_positive (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    1 ≤ entryAnchorA p k := by
  have h := p.entry_column_triangle_room k hk
  unfold entryAnchorA
  omega

def entryUp (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (2 * p.entrySkin k - 1) :=
  borrowedPrefixFold p.side (entryAnchorA p k) (3 * (k + 1)) 0
    (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) (2 * p.entrySkin k - 1)

def entryTargetColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    DanglingColumn p.side := faceDanglingColumn p.side
      (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
      (by have h := p.separator_room k hk; omega)

theorem separatorIndex_ge_two (p : ConstructionParameters) (k : ℕ) : 2 ≤ p.separatorIndex k := by
  have h := p.leftFiller_ge
  unfold ConstructionParameters.separatorIndex
  omega

theorem entryUp_row_disjoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (entryRowCount p k)) :
    (entryUp p k hk).pos i ≠ (entryRowFold p k hk).pos j := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  have ha := entryAnchor_positive p k hk
  have hs := entryAnchor_equation p k hk
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun q => (entryUp p k hk).pos i ≠ q) ?_ ?_ j
  · intro r
    have heq : p.side - 3 - 3 * (k + 1) + p.entrySkin k =
        entryAnchorA p k - 1 + p.entrySkin k := by unfold entryAnchorA; omega
    change borrowedPoint p.side (entryAnchorA p k) (3 * (k + 1)) 0
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) i.val ≠
      faceRowPoint 2 p.side (p.entrySkin k)
        (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) 1
        (entryRow_faceEquation p k hk) r.val
    simpa only [heq] using borrowedPoint_ne_entryRowC p.side (entryAnchorA p k)
      (3 * (k + 1)) (p.entrySkin k) i.val r.val hs ha hj.1 i.isLt
  · intro r heq
    dsimp only [rowFold] at heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    apply hfree
    rw [← heq]
    exact borrowedPoint_on_column p.side (entryAnchorA p k) (3 * (k + 1)) 0 hs ha i.val

theorem entryRow_ne_targetColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (n : ℕ) :
    (entryRowFold p k hk).pos i ≠ (entryTargetColumn p k hk).point n := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun q => q ≠ (entryTargetColumn p k hk).point n) ?_ ?_ i
  · intro r
    exact entryRowC_ne_farColumn p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k)
      (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k) r.val n
      (entryRow_faceEquation p k hk) (by have h := p.separator_room k hk; omega)
      (separatorIndex_ge_two p k)
  · intro r heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    exact hfree ⟨entryTargetColumn p k hk, n, heq.symm⟩

theorem entryUp_ne_targetColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (n : ℕ) :
    (entryUp p k hk).pos i ≠ (entryTargetColumn p k hk).point n :=
  borrowedPoint_ne_farColumn p.side (entryAnchorA p k) (3 * (k + 1))
    (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k) i.val n
    (entryAnchor_equation p k hk) (by have h := p.separator_room k hk; omega)
    (entryAnchor_positive p k hk) (separatorIndex_ge_two p k)

end ProteinFolding.Tetrahedral.NearField
