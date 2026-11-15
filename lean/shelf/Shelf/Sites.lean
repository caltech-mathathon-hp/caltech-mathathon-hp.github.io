import Shelf.FoldBasics

/-!
# Sites by coordinates

Section 5 of the paper builds a fold by writing down sites: `(1, N + 1, N - 1)`,
"the sites `(1, y, -1)` for `y = N, …, 0`", and so on. This file has the notation
for that: `pt x y z` is the site with these coordinates, and `line a e r` is the
row of `r` sites `a, a + e, a + 2e, …`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding

/-- The site with coordinates `(x, y, z)`. -/
def pt (x y z : ℤ) : Site := ![x, y, z]

@[simp] theorem pt_apply_zero (x y z : ℤ) : pt x y z 0 = x := rfl
@[simp] theorem pt_apply_one (x y z : ℤ) : pt x y z 1 = y := rfl
@[simp] theorem pt_apply_two (x y z : ℤ) : pt x y z 2 = z := rfl

/-- Two sites with the same three coordinates are equal. -/
theorem site_ext {p q : Site} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) : p = q := by
  funext k
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2

theorem pt_eta (p : Site) : pt (p 0) (p 1) (p 2) = p :=
  site_ext rfl rfl rfl

theorem pt_eq_iff {x y z x' y' z' : ℤ} :
    pt x y z = pt x' y' z' ↔ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

@[simp] theorem pt_add (x y z x' y' z' : ℤ) :
    pt x y z + pt x' y' z' = pt (x + x') (y + y') (z + z') :=
  site_ext rfl rfl rfl

@[simp] theorem pt_sub (x y z x' y' z' : ℤ) :
    pt x y z - pt x' y' z' = pt (x - x') (y - y') (z - z') :=
  site_ext rfl rfl rfl

theorem latticeDistance_pt (x y z x' y' z' : ℤ) :
    latticeDistance (pt x y z) (pt x' y' z') =
      (x - x').natAbs + (y - y').natAbs + (z - z').natAbs := by
  rw [latticeDistance_eq]
  rfl

theorem adj_pt {x y z x' y' z' : ℤ} :
    cubicLattice.Adj (pt x y z) (pt x' y' z') ↔
      (x - x').natAbs + (y - y').natAbs + (z - z').natAbs = 1 := by
  rw [adj_iff, latticeDistance_pt]

theorem pt_mem_Q {n : ℕ} {x y z : ℤ} :
    pt x y z ∈ Q n ↔ (0 ≤ x ∧ x < n) ∧ (0 ≤ y ∧ y < n) ∧ (0 ≤ z ∧ z < n) := by
  rw [mem_Q]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ k
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2

/-- The row of `r` sites `a, a + e, …, a + (r - 1) e`. -/
def line (a e : Site) (r : ℕ) : List Site :=
  (List.range r).map fun (t : ℕ) (k : Fin 3) => a k + (t : ℤ) * e k

@[simp] theorem line_length (a e : Site) (r : ℕ) : (line a e r).length = r := by
  simp [line]

theorem mem_line {a e : Site} {r : ℕ} {p : Site} :
    p ∈ line a e r ↔ ∃ t, t < r ∧ ∀ k, p k = a k + (t : ℤ) * e k := by
  unfold line
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, List.mem_range.mp ht, fun _ => rfl⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, List.mem_range.mpr ht, (funext h).symm⟩

end ProteinFolding.Shelf
