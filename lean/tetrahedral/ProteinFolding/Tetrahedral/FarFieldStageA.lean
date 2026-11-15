import ProteinFolding.Tetrahedral.FarFieldWireColumns

/-! Stage A for a finite family of outward columns: construct each avenue
through the assigned column top and prove all column/avenue separation from
the actual arm identities and the constructed reverse-X level ranks. -/

namespace ProteinFolding.Tetrahedral.FarField

def levelAvenue {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) (x : ℤ) : Site :=
  wireAvenue R hR (quadrants i) (columnTop R hR H quadrants bases i) x

theorem levelAvenue_profile {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) (x : ℤ)
    (hp : PositiveQuadrant R (bases i)) (hbelow : rho R (bases i) ≤ H)
    (hhigh : |alpha R (bases i)| + 8 < H) :
    InQuadrant R (quadrants i) (levelAvenue R hR H quadrants bases i x) ∧
      (rho R (levelAvenue R hR H quadrants bases i x) = wireLevels H quadrants bases i ∨
        rho R (levelAvenue R hR H quadrants bases i x) = wireLevels H quadrants bases i + 2) ∧
      (alpha R (levelAvenue R hR H quadrants bases i x) = alpha R (bases i) ∨
        alpha R (levelAvenue R hR H quadrants bases i x) = alpha R (bases i) + 2) := by
  have ht := columnTop_profile R hR H hH quadrants bases i hp hbelow
  have hlev := (assignedLevel_bounds H (wireBaseXs quadrants bases) i).1
  change H ≤ wireLevels H quadrants bases i at hlev
  have htop : |alpha R (columnTop R hR H quadrants bases i)| + 8 < rho R (columnTop R hR H quadrants bases i) := by
    rw [ht.2.1, ht.2.2.1]
    omega
  have hmem := wireAvenue_member R hR (quadrants i) (columnTop R hR H quadrants bases i) x ht.1 htop
  simpa only [AvenueMembership, levelAvenue, ht.2.1, ht.2.2.1] using hmem

@[simp] theorem levelAvenue_x {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) (x : ℤ) :
    X (levelAvenue R hR H quadrants bases i x) = x := wireAvenue_x _ _ _ _ _

theorem levelAvenue_self {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w)
    (hp : PositiveQuadrant R (bases i)) (hbelow : rho R (bases i) ≤ H)
    (hhigh : |alpha R (bases i)| + 8 < H) :
    levelAvenue R hR H quadrants bases i (X (columnTop R hR H quadrants bases i)) = columnTop R hR H quadrants bases i := by
  have ht := columnTop_profile R hR H hH quadrants bases i hp hbelow
  have hlev := (assignedLevel_bounds H (wireBaseXs quadrants bases) i).1
  apply wireAvenue_self R hR _ _ ht.1
  rw [ht.2.1, ht.2.2.1]
  change H ≤ wireLevels H quadrants bases i at hlev
  omega

theorem same_level_strips_separated {w : ℕ} (R : ℤ) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site)
    (hp : ∀ i, PositiveQuadrant R (bases i))
    (hids : Function.Injective (fun i => armIdentity R (quadrants i) (bases i)))
    (i j : Fin w) (hne : i ≠ j) (hq : quadrants i = quadrants j)
    (hlev : wireLevels H quadrants bases i = wireLevels H quadrants bases j) :
    alpha R (bases i) + 4 ≤ alpha R (bases j) ∨ alpha R (bases j) + 4 ≤ alpha R (bases i) := by
  have hbase : wireBaseXs quadrants bases i = wireBaseXs quadrants bases j :=
    (assignedLevel_eq_iff H (wireBaseXs quadrants bases) i j).1 hlev
  have hband : quadrantArmBaseX (quadrants i) (bases i) = quadrantArmBaseX (quadrants i) (bases j) := by
    simpa only [wireBaseXs, ← hq] using hbase
  have hα : alpha R (bases i) ≠ alpha R (bases j) := by
    intro h
    apply hne
    apply hids
    apply Prod.ext
    · exact hq
    · apply Prod.ext
      · exact hbase
      · exact h
  exact separated_arm_strips R (quadrants i) (bases i) (bases j) (hp i) (hp j) hband hα

theorem levelAvenues_disjoint {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site)
    (hp : ∀ i, PositiveQuadrant R (bases i)) (hbelow : ∀ i, rho R (bases i) ≤ H)
    (hhigh : ∀ i, |alpha R (bases i)| + 8 < H)
    (hids : Function.Injective (fun i => armIdentity R (quadrants i) (bases i)))
    (i j : Fin w) (hne : i ≠ j) (x y : ℤ) :
    levelAvenue R hR H quadrants bases i x ≠ levelAvenue R hR H quadrants bases j y := by
  intro heq
  have hi := levelAvenue_profile R hR H hH quadrants bases i x (hp i) (hbelow i) (hhigh i)
  have hj := levelAvenue_profile R hR H hH quadrants bases j y (hp j) (hbelow j) (hhigh j)
  rw [← heq] at hj
  have hq := quadrant_unique R (quadrants i) (quadrants j) _ hi.1 hj.1
  by_cases hlev : wireLevels H quadrants bases i = wireLevels H quadrants bases j
  · have hsep := same_level_strips_separated R H quadrants bases hp hids i j hne hq hlev
    omega
  · have hsep := assignedLevel_separated H (wireBaseXs quadrants bases) i j hlev
    change wireLevels H quadrants bases i + 4 ≤ wireLevels H quadrants bases j ∨
      wireLevels H quadrants bases j + 4 ≤ wireLevels H quadrants bases i at hsep
    omega

theorem levelAvenue_other_column {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site)
    (hp : ∀ i, PositiveQuadrant R (bases i)) (hbelow : ∀ i, rho R (bases i) ≤ H)
    (hhigh : ∀ i, |alpha R (bases i)| + 8 < H)
    (hids : Function.Injective (fun i => armIdentity R (quadrants i) (bases i)))
    (i j : Fin w) (hne : i ≠ j) (x : ℤ) (hx : X (columnTop R hR H quadrants bases i) ≤ x)
    (k : Fin (columnHeight R H quadrants bases j + 1)) :
    levelAvenue R hR H quadrants bases i x ≠ (columnFold R hR H quadrants bases j).pos k := by
  intro heq
  have hi := levelAvenue_profile R hR H hH quadrants bases i x (hp i) (hbelow i) (hhigh i)
  have hj := columnFold_profile R hR H hH quadrants bases j (hp j) (hbelow j) k
  have ht := columnTop_profile R hR H hH quadrants bases i (hp i) (hbelow i)
  rw [← heq] at hj
  have hq := quadrant_unique R (quadrants i) (quadrants j) _ hi.1 hj.1
  rcases lt_trichotomy (wireLevels H quadrants bases j) (wireLevels H quadrants bases i) with hlt | hlev | hgt
  · omega
  · have hsep := same_level_strips_separated R H quadrants bases hp hids i j hne hq hlev.symm
    omega
  · have hb := assignedLevel_reverse_order H (wireBaseXs quadrants bases) i j hgt
    change wireBaseXs quadrants bases j < wireBaseXs quadrants bases i at hb
    have hxp := congrArg X heq
    simp only [levelAvenue_x] at hxp
    have hxx : x = X (columnTop R hR H quadrants bases i) := by
      simp only [levelAvenue_x] at hj
      omega
    have htop := levelAvenue_self R hR H hH quadrants bases i (hp i) (hbelow i) (hhigh i)
    rw [hxx, htop] at heq
    have harm : quadrantArm R hR (quadrants i) (bases i) (columnHeight R H quadrants bases i) =
        quadrantArm R hR (quadrants j) (bases j) k.val := by
      simpa only [columnTop, columnFold, intervalFold, ite_true, zero_add] using heq
    exact hne (hids (arm_identity_of_intersect R hR _ _ _ _ (hp i) (hp j) _ _ (by omega) (by omega) harm))

end ProteinFolding.Tetrahedral.FarField
