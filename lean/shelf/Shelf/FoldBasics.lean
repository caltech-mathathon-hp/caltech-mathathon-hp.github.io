import Shelf.Cube

/-!
# Folds, with letters numbered by natural numbers

The team's `Fold` places letter `i : Fin N` at `f.pos i`. The proofs of our write-up
talk about "the letter after `i`" and "the letters between `i` and `j`", which is
easier with natural numbers: `site f i` is the site of letter `i` (counting from
0), and `S[i]? = some H` says that letter `i` exists and is an `H`.

`Fills S f n` says that the `H`'s occupy exactly the cube `Q n = {0, …, n-1}³`.
This is a perfect fold "translated so that the H's occupy Q", the standing
assumption of Sections 2.2 and 4 of our write-up; `perfect_iff_exists_fills` does the translation.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue

/-! ## Distance -/

theorem latticeDistance_eq (x y : Site) :
    latticeDistance x y =
      (x 0 - y 0).natAbs + (x 1 - y 1).natAbs + (x 2 - y 2).natAbs := by
  simp [latticeDistance, Fin.sum_univ_three]

theorem adj_iff {x y : Site} : cubicLattice.Adj x y ↔ latticeDistance x y = 1 := Iff.rfl

theorem latticeDistance_self (x : Site) : latticeDistance x x = 0 := by
  simp [latticeDistance]

theorem latticeDistance_triangle (x y z : Site) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  simp only [latticeDistance_eq]
  omega

theorem latticeDistance_sub_right (x y a : Site) :
    latticeDistance (x - a) (y - a) = latticeDistance x y := by
  simp [latticeDistance_eq]

/-! ## Letters numbered by natural numbers -/

variable {N : ℕ}

/-- The site of letter `i`, counting from 0. For `i ≥ N` the value is not used. -/
def site (f : Fold cubicLattice N) (i : ℕ) : Site :=
  if h : i < N then f.pos ⟨i, h⟩ else 0

theorem site_eq (f : Fold cubicLattice N) {i : ℕ} (h : i < N) : site f i = f.pos ⟨i, h⟩ := by
  simp [site, h]

/-- Consecutive letters sit on adjacent sites. -/
theorem site_adj (f : Fold cubicLattice N) {i : ℕ} (h : i + 1 < N) :
    cubicLattice.Adj (site f i) (site f (i + 1)) := by
  rw [site_eq f (Nat.lt_of_succ_lt h), site_eq f h]
  exact f.consecutive _ _ rfl

/-- Different letters sit on different sites. -/
theorem site_inj (f : Fold cubicLattice N) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : site f i = site f j) : i = j := by
  rw [site_eq f hi, site_eq f hj] at h
  exact congrArg Fin.val (f.injective_pos h)

/-- Letters `i ≤ j` are joined by a walk of `j - i` steps, so their sites are at
distance at most `j - i`. -/
theorem latticeDistance_site_le (f : Fold cubicLattice N) {i j : ℕ} (hij : i ≤ j)
    (hj : j < N) : latticeDistance (site f i) (site f j) ≤ j - i := by
  induction j, hij using Nat.le_induction with
  | base => simp [latticeDistance_self]
  | succ j hij ih =>
    have h1 := ih (Nat.lt_of_succ_lt hj)
    have h2 : latticeDistance (site f j) (site f (j + 1)) = 1 := site_adj f hj
    have h3 := latticeDistance_triangle (site f i) (site f j) (site f (j + 1))
    omega

/-! ## Perfect folds in standard position -/

/-- The `H`'s of `S` occupy exactly the cube `Q n`. -/
def Fills (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) : Prop :=
  hydrophobicSites S f = Q n

variable {S : Sequence} {f : Fold cubicLattice S.length} {n : ℕ}

/-- Every `H` is in the cube. -/
theorem Fills.site_mem (hf : Fills S f n) {i : ℕ} (h : S[i]? = some H) : site f i ∈ Q n := by
  obtain ⟨hi, hH⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hf, site_eq f hi]
  exact ⟨⟨i, hi⟩, hH, rfl⟩

/-- Every `P` is outside the cube. -/
theorem Fills.site_not_mem (hf : Fills S f n) {i : ℕ} (h : S[i]? = some P) :
    site f i ∉ Q n := by
  obtain ⟨hi, hP⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hf, site_eq f hi]
  rintro ⟨j, hj, hpos⟩
  have hji : j = ⟨i, hi⟩ := f.injective_pos hpos
  subst hji
  have : S[i] = H := hj
  rw [hP] at this
  exact Residue.noConfusion this

/-- Every site of the cube carries an `H`. -/
theorem Fills.exists_index (hf : Fills S f n) {p : Site} (hp : p ∈ Q n) :
    ∃ i, S[i]? = some H ∧ site f i = p := by
  rw [← hf] at hp
  obtain ⟨j, hj, hpos⟩ := hp
  refine ⟨j.val, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩
  · rw [site_eq f j.isLt]
    exact hpos

/-- A fold moved by the vector `-a`. -/
def translate (f : Fold cubicLattice N) (a : Site) : Fold cubicLattice N where
  pos i := f.pos i - a
  injective_pos i j h := f.injective_pos (sub_left_injective h)
  consecutive i j h := by
    have := f.consecutive i j h
    rw [adj_iff] at this ⊢
    rw [latticeDistance_sub_right]
    exact this

/-- "After a translation the `H`'s occupy `Q`": a string has a perfect fold if
and only if it has a fold whose `H`'s occupy exactly `Q n`. -/
theorem exists_packsCube_iff_exists_fills (S : Sequence) (n : ℕ) :
    (∃ f : Fold cubicLattice S.length, PacksCube S f n) ↔
      ∃ f : Fold cubicLattice S.length, Fills S f n := by
  constructor
  · rintro ⟨f, a, ha⟩
    refine ⟨translate f a, ?_⟩
    ext p
    constructor
    · rintro ⟨i, hi, hpos⟩
      have hmem : f.pos i ∈ cube a n := by
        rw [← ha]
        exact ⟨i, hi, rfl⟩
      rw [mem_Q]
      intro k
      have hk := hmem k
      have hpk : p k = f.pos i k - a k := by
        rw [← hpos]
        rfl
      omega
    · intro hp
      rw [mem_Q] at hp
      have hmem : p + a ∈ cube a n := by
        intro k
        have hk := hp k
        simp only [Pi.add_apply]
        omega
      rw [← ha] at hmem
      obtain ⟨i, hi, hpos⟩ := hmem
      refine ⟨i, hi, ?_⟩
      show f.pos i - a = p
      rw [hpos]
      simp
  · rintro ⟨f, hf⟩
    exact ⟨f, 0, hf⟩

theorem perfect_iff_exists_fills (S : Sequence) (n : ℕ) :
    PerfectHPStringFold S n ↔
      hydrophobicCount S = n ^ 3 ∧ ∃ f : Fold cubicLattice S.length, Fills S f n := by
  unfold PerfectHPStringFold
  rw [exists_packsCube_iff_exists_fills]

end ProteinFolding.Shelf
