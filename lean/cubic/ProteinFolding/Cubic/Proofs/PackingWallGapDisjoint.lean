import ProteinFolding.Cubic.Proofs.PackingGapFold
import ProteinFolding.Cubic.Proofs.PackingPrefixWallsDisjoint

/-! The two gap H sites in each period are precisely the right-rail sites
omitted by every wall unit. Disjoint H owners separate all of their exterior
decorations as well. These lemmas do not import the assembled walls. -/

namespace ProteinFolding.CubicPackingWalls

open CubicPacking CubicCertificates CubicPackingLift CubicPackingRouting

theorem multiple_not_between_zero_and_period (b s r : ℤ) (hr : 0 < r) (hrb : r < b)
    (he : s * b = r) : False := by
  have hm := congrArg (fun z : ℤ => z % b) he
  dsimp only at hm
  rw [Int.mul_emod_left, Int.emod_eq_of_lt (by omega) hrb] at hm
  omega

theorem wallTop_multiple (q Q : ℕ) (k : Fin q) :
    wallTop q Q k = ((q : ℤ) - k.val) * beta Q := by
  simp only [wallTop, depth, Nat.cast_mul]
  ring

theorem unitOwners_ne_gap (q Q : ℕ) (k j : Fin q)
    (i : Fin (alpha Q + (depth q Q + ((2 * alpha Q + 2) + (depth q Q + alpha Q)))))
    (e : Fin 2) :
    unitOwners (depth q Q) (alpha Q) (wallTop q Q k) i ≠
      point (depth q Q + 1) ((alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q + e.val) 0 := by
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  have he0 := e.isLt
  cases i using Fin.addCases with
  | left i =>
    have hi := i.isLt
    simp only [unitOwners, Fin.append_left] at hy
    change wallTop q Q k - alpha Q + 1 + i.val =
      (alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q + e.val at hy
    rw [wallTop_multiple] at hy
    apply multiple_not_between_zero_and_period (beta Q)
      ((q : ℤ) - k.val - j.val) (2 * (alpha Q : ℤ) + e.val - i.val)
    · omega
    · omega
    · nlinarith
  | right i =>
    simp only [unitOwners, Fin.append_right] at hx hy
    cases i using Fin.addCases with
    | left i =>
      have hi := i.isLt
      simp only [Fin.append_left] at hx
      change (depth q Q : ℤ) - i.val = ((depth q Q + 1 : ℕ) : ℤ) at hx
      omega
    | right i =>
      simp only [Fin.append_right] at hx hy
      cases i using Fin.addCases with
      | left i =>
        simp only [Fin.append_left] at hx
        change (0 : ℤ) = ((depth q Q + 1 : ℕ) : ℤ) at hx
        omega
      | right i =>
        simp only [Fin.append_right] at hx hy
        cases i using Fin.addCases with
        | left i =>
          have hi := i.isLt
          simp only [Fin.append_left] at hx
          change (i.val : ℤ) + 1 = ((depth q Q + 1 : ℕ) : ℤ) at hx
          omega
        | right i =>
          have hi := i.isLt
          simp only [Fin.append_right] at hy
          change wallTop q Q k - ((2 * alpha Q + 2 : ℕ) : ℤ) + 1 + i.val =
            (alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q + e.val at hy
          rw [wallTop_multiple] at hy
          apply multiple_not_between_zero_and_period (beta Q)
            ((q : ℤ) - k.val - j.val - 1) ((alpha Q : ℤ) + e.val - i.val)
          · omega
          · omega
          · push_cast at hy
            nlinarith

def gapOwners (d : ℕ) (y : ℤ) (e : Fin 2) : Site := point (d + 1) (y + e.val) 0

theorem gapOwners_inside (d : ℕ) (y : ℤ) (hy : 1 ≤ y ∧ y + 1 ≤ d) (e : Fin 2) :
    gapOwners d y e ∈ cube (fun _ => 0) (d + 2) := by
  have he := e.isLt
  intro axis
  match axis with
  | 0 => change (0 : ℤ) ≤ (d : ℤ) + 1 ∧ (d : ℤ) + 1 < 0 + ((d + 2 : ℕ) : ℤ); omega
  | 1 => change (0 : ℤ) ≤ y + e.val ∧ y + e.val < 0 + ((d + 2 : ℕ) : ℤ); omega
  | 2 => change (0 : ℤ) ≤ 0 ∧ 0 < 0 + ((d + 2 : ℕ) : ℤ); omega

theorem gapEdgeFold_attached (d : ℕ) (y : ℤ) (hy : 1 ≤ y ∧ y + 1 ≤ d) :
    AttachedTo (fun _ => 0) (d + 2) (gapEdgeFold d y) (gapOwners d y) := by
  refine ⟨gapOwners_inside d y hy, ?_⟩
  intro i
  refine ⟨⟨if i.val < 3 then 0 else 1, by split_ifs <;> decide⟩, ?_⟩
  fin_cases i
  all_goals first
    | solve
      | apply Or.inl
        apply site_ext <;> simp [gapEdgeFold, gapEdgePos, gapOwners, point]
    | apply Or.inr; constructor
      · intro hp
        first
        | solve
          | have hz := (hp 2).1; norm_num [gapEdgeFold, gapEdgePos, point] at hz
        | solve
          | have hx := (hp 0).2; simp [gapEdgeFold, gapEdgePos, point] at hx <;> omega
      · change latticeDistance _ _ = 1
        rw [distance_eq]
        simp [gapEdgeFold, gapEdgePos, gapOwners, point]

theorem gapRow_bounds (q Q : ℕ) (j : Fin q) :
    1 ≤ (alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q ∧
      (alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q + 1 ≤ depth q Q := by
  have hm := Nat.mul_le_mul_right (beta Q) (show j.val + 1 ≤ q by omega)
  have hm' : ((j.val : ℤ) + 1) * beta Q ≤ (depth q Q : ℤ) := by
    simpa only [depth, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      (show (((j.val + 1) * beta Q : ℕ) : ℤ) ≤ ((q * beta Q : ℕ) : ℤ) from by exact_mod_cast hm)
  have hb : (beta Q : ℤ) = 2 * (alpha Q : ℤ) + 2 := by dsimp [beta, alpha]; omega
  have hnon : 0 ≤ (j.val : ℤ) * beta Q := by positivity
  rw [add_mul, one_mul] at hm'
  omega

/-- A complete wall unit and any of the actual E₂ gap blocks are disjoint,
including every P attachment. -/
theorem wallUnit_gapEdge_disjoint (q Q : ℕ) (k j : Fin q)
    (f : Fold cubicLattice (wallUnit q Q).length)
    (hf : AttachedTo (fun _ => 0) (side q Q) f
      (unitOwners (depth q Q) (alpha Q) (wallTop q Q k))) :
    ∀ i l, f.pos i ≠
      (gapEdgeFold (depth q Q) ((alpha Q : ℤ) + 1 + (j.val : ℤ) * beta Q)).pos l := by
  apply attached_folds_disjoint (fun _ => 0) (side q Q) f _ _ _ hf
    (gapEdgeFold_attached _ _ (gapRow_bounds q Q j))
  exact unitOwners_ne_gap q Q k j

end ProteinFolding.CubicPackingWalls
