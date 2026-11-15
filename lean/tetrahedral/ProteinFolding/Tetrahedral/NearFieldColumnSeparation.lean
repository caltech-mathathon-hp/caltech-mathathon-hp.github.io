import ProteinFolding.Tetrahedral.NearFieldEntryOrdering

/-! Distinct actual source and separator columns remain disjoint after the
one-bond borrowing at an entry cap. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem faceColumn_seed_ne_of_b_ne (m a b c A B C : ℕ)
    (hs : a + b + c + 2 = m) (ht : A + B + C + 2 = m) (hne : b ≠ B) :
    (faceDanglingColumn m a b c hs).seed ≠ (faceDanglingColumn m A B C ht).seed := by
  intro heq
  have hy := congrArg (fun q : Site => q.val 1) heq
  dsimp only at hy
  rw [faceDanglingColumn_seed, faceDanglingColumn_seed] at hy
  dsimp [faceSubSite, faceSubCoordinates] at hy
  exact hne (by omega)

theorem faceColumn_seed_ne_of_c_ne (m a b c A B C : ℕ)
    (hs : a + b + c + 2 = m) (ht : A + B + C + 2 = m) (hne : c ≠ C) :
    (faceDanglingColumn m a b c hs).seed ≠ (faceDanglingColumn m A B C ht).seed := by
  intro heq
  have hx := congrArg (fun q : Site => q.val 0) heq
  dsimp only at hx
  rw [faceColumn_seed_x, faceColumn_seed_x] at hx
  exact hne (by omega)

theorem borrowedPoint_disjoint_of_b_ne (m a b A B n r : ℕ)
    (hs : a + b + 0 + 2 = m) (ht : A + B + 0 + 2 = m)
    (ha : 1 ≤ a) (hA : 1 ≤ A) (hne : b ≠ B) :
    borrowedPoint m a b 0 hs ha n ≠ borrowedPoint m A B 0 ht hA r := by
  intro heq
  cases n with
  | zero =>
    cases r with
    | zero => exact faceColumn_seed_ne_of_b_ne m a b 0 A B 0 hs ht hne heq
    | succ r =>
      have hx := congrArg (fun q : Site => q.val 0) heq
      dsimp only [borrowedPoint] at hx
      rw [faceColumn_seed_x, faceDanglingColumn_point_coordinates] at hx
      omega
  | succ n =>
    cases r with
    | zero =>
      have hx := congrArg (fun q : Site => q.val 0) heq
      dsimp only [borrowedPoint] at hx
      rw [faceDanglingColumn_point_coordinates, faceColumn_seed_x] at hx
      omega
    | succ r =>
      have hseeds := DanglingColumn.seeds_eq_of_point_eq
        (faceDanglingColumn m (a - 1) b (0 + 1) (by omega))
        (faceDanglingColumn m (A - 1) B (0 + 1) (by omega)) heq
      exact faceColumn_seed_ne_of_b_ne m (a - 1) b (0 + 1) (A - 1) B (0 + 1)
        (by omega) (by omega) hne hseeds

theorem separatorIndex_injective (p : ConstructionParameters) : Function.Injective p.separatorIndex := by
  intro k l heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmul := Nat.mul_lt_mul_of_pos_right h (by omega : 0 < p.binDimers + 2)
    unfold ConstructionParameters.separatorIndex at heq
    omega
  · have hmul := Nat.mul_lt_mul_of_pos_right h (by omega : 0 < p.binDimers + 2)
    unfold ConstructionParameters.separatorIndex at heq
    omega

theorem entryUps_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (2 * p.entrySkin l - 1)) :
    (entryUp p k hk).pos i ≠ (entryUp p l hl).pos j :=
  borrowedPoint_disjoint_of_b_ne p.side (entryAnchorA p k) (3 * (k + 1))
    (entryAnchorA p l) (3 * (l + 1)) i.val j.val
    (entryAnchor_equation p k hk) (entryAnchor_equation p l hl)
    (entryAnchor_positive p k hk) (entryAnchor_positive p l hl) (by omega)

theorem entryUps_downs_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (2 * p.entrySkin l - 1)) :
    (entryUp p k hk).pos i ≠ (entryDown p l hl).pos j :=
  borrowedPoint_ne_farColumn p.side (entryAnchorA p k) (3 * (k + 1))
    (p.side - 2 - p.separatorIndex l) 0 (p.separatorIndex l) i.val j.rev.val
    (entryAnchor_equation p k hk) (by have h := p.separator_room l hl; omega)
    (entryAnchor_positive p k hk) (separatorIndex_ge_two p l)

theorem entryDowns_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (2 * p.entrySkin k - 1)) (j : Fin (2 * p.entrySkin l - 1)) :
    (entryDown p k hk).pos i ≠ (entryDown p l hl).pos j := by
  apply DanglingColumn.points_ne_of_seed_ne
  exact faceColumn_seed_ne_of_c_ne p.side _ _ _ _ _ _ _ _
    (fun h => hne (separatorIndex_injective p h))

end ProteinFolding.Tetrahedral.NearField
