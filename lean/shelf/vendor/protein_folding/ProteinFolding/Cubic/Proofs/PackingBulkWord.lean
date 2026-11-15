import ProteinFolding.Cubic.Proofs.PackingSnakeCuboid
import ProteinFolding.Cubic.Proofs.PackingRoutingRectangle
import ProteinFolding.Common.FoldConcatenation
import Mathlib.Tactic.Ring

/-! Literal bulk H block and its exterior approach to the first wall. The
interior snake is bracketed by the two omitted sites of the top face. The
following P path has exactly alpha+8 vertices and stays off the H support. -/

namespace ProteinFolding.CubicPackingBulk

open CubicCertificates CubicPackingSnake CubicPackingRouting

def upperHole (d : ℕ) : Site := point d (d + 1) d
def lowerHole (d : ℕ) : Site := point d (d + 1) 1

def singleFold (p : Site) : Fold cubicLattice 1 where
  pos _ := p
  injective_pos := by intro i j _; apply Fin.ext; have := i.isLt; have := j.isLt; omega
  consecutive := by intro i j hij; have := i.isLt; have := j.isLt; omega

theorem singleFold_sites (p q : Site) : (∃ i, (singleFold p).pos i = q) ↔ q = p := by
  constructor
  · rintro ⟨i, hi⟩; exact hi.symm
  · rintro rfl; exact ⟨⟨0, by omega⟩, rfl⟩

theorem onLength_sites {N M : ℕ} (f : Fold cubicLattice N) (h : M = N) (p : Site) :
    (∃ i, (f.onLength h).pos i = p) ↔ ∃ j, f.pos j = p := by
  subst M
  rfl

theorem upper_interior_disjoint (d : ℕ) :
    ∀ i j, (singleFold (upperHole d)).pos i ≠ interiorPos d j := by
  intro i j he
  have hp := (interiorPos_cube_iff d _).mp ⟨j, rfl⟩ 1
  have hy := congrFun he 1
  change (d : ℤ) + 1 = interiorPos d j 1 at hy
  change 1 ≤ interiorPos d j 1 ∧ interiorPos d j 1 < 1 + (d : ℤ) at hp
  omega

theorem upper_interior_seam (d : ℕ) (hd : 0 < d) :
    ∀ i : Fin 1, ∀ j : Fin (d * (d * d)), i.val + 1 = 1 → j.val = 0 →
      cubicLattice.Adj ((singleFold (upperHole d)).pos i) ((interiorFold d hd).pos j) := by
  intro i j _ hj
  have he : j = firstIndex d (d*d) hd (Nat.mul_pos hd hd) := Fin.ext hj
  change latticeDistance (upperHole d) (interiorPos d j) = 1
  rw [he, interiorPos_first, distance_eq]
  simp [upperHole, point]

def upperInteriorFold (d : ℕ) (hd : 0 < d) : Fold cubicLattice (1 + d*(d*d)) :=
  Fold.append (singleFold (upperHole d)) (interiorFold d hd)
    (upper_interior_disjoint d) (upper_interior_seam d hd)

theorem upperInterior_lower_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    ∀ i j, (upperInteriorFold d hd).pos i ≠ (singleFold (lowerHole d)).pos j := by
  intro i j he
  cases i using Fin.addCases with
  | left i =>
    have hz := congrFun he 2
    simp only [upperInteriorFold, Fold.append_pos_left] at hz
    change (d : ℤ) = 1 at hz
    omega
  | right i =>
    have hp := (interiorPos_cube_iff d _).mp ⟨i, rfl⟩ 1
    have hy := congrFun he 1
    simp only [upperInteriorFold, Fold.append_pos_right] at hy
    change interiorPos d i 1 = (d : ℤ) + 1 at hy
    change 1 ≤ interiorPos d i 1 ∧ interiorPos d i 1 < 1 + (d : ℤ) at hp
    omega

theorem upperInterior_lower_seam (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    ∀ i : Fin (1 + d*(d*d)), ∀ j : Fin 1,
      i.val + 1 = 1 + d*(d*d) → j.val = 0 →
      cubicLattice.Adj ((upperInteriorFold d hd).pos i) ((singleFold (lowerHole d)).pos j) := by
  intro i j hi _
  cases i using Fin.addCases with
  | left i =>
    have hpos := Nat.mul_pos hd (Nat.mul_pos hd hd)
    have hil := i.isLt
    change i.val + 1 = 1 + d*(d*d) at hi
    omega
  | right i =>
    have hi' : i.val + 1 = d*(d*d) := by change 1 + i.val + 1 = _ at hi; omega
    have hei : i = lastIndex d (d*d) hd (Nat.mul_pos hd hd) := by
      apply Fin.ext
      change i.val = d*(d*d)-1
      omega
    simp only [upperInteriorFold, Fold.append_pos_right]
    change latticeDistance (interiorPos d i) (lowerHole d) = 1
    rw [hei, interiorPos_last_even d hd heven, distance_eq]
    simp [lowerHole, point]

def bulkFold (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) : Fold cubicLattice (d^3+2) :=
  (Fold.append (upperInteriorFold d hd) (singleFold (lowerHole d))
    (upperInterior_lower_disjoint d hd heven) (upperInterior_lower_seam d hd heven)).onLength (by ring)

/-- The bulk block visits the entire d-cube interior and the two top holes. -/
theorem bulkFold_sites (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (p : Site) :
    (∃ i, (bulkFold d hd heven).pos i = p) ↔
      p = upperHole d ∨ p ∈ cube (fun _ => 1) d ∨ p = lowerHole d := by
  rw [bulkFold, onLength_sites, Fold.append_exists_pos]
  simp only [upperInteriorFold, Fold.append_exists_pos, singleFold_sites,
    interiorFold, interiorPos_cube_iff]
  tauto

theorem bulkFold_first (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (d^3+2)) (hi : i.val = 0) : (bulkFold d hd heven).pos i = upperHole d := by
  change Fin.append (Fin.append (fun _ => upperHole d) (interiorPos d))
    (fun _ => lowerHole d) (Fin.cast _ i) = _
  have he : Fin.cast (by ring : d^3+2 = (1+d*(d*d))+1) i =
      Fin.castAdd 1 (Fin.castAdd (d*(d*d)) (⟨0, by omega⟩ : Fin 1)) := Fin.ext hi
  rw [he, Fin.append_left, Fin.append_left]

theorem bulkFold_last (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (d^3+2)) (hi : i.val + 1 = d^3+2) : (bulkFold d hd heven).pos i = lowerHole d := by
  change Fin.append (Fin.append (fun _ => upperHole d) (interiorPos d))
    (fun _ => lowerHole d) (Fin.cast _ i) = _
  have he : Fin.cast (by ring : d^3+2 = (1+d*(d*d))+1) i =
      Fin.natAdd (1+d*(d*d)) (⟨0, by omega⟩ : Fin 1) := by
    apply Fin.ext
    change i.val = (1+d*(d*d))+0
    have hp : d^3 = d*(d*d) := by ring
    omega
  rw [he, Fin.append_right]

/-- The P vertices after the bulk end; the initial H is excluded. -/
def approachPoint (d : ℕ) (k : ℕ) : Site :=
  if k < 2 then point d ((d : ℤ)+2+k) 1
  else if k < 5 then point d ((d : ℤ)+3) (2-(k : ℤ))
  else if k < 6 then point ((d : ℤ)+1) ((d : ℤ)+3) (-2)
  else point ((d : ℤ)+1) ((d : ℤ)+8-k) (-2)

def approachPos (d alpha : ℕ) (i : Fin (alpha+8)) : Site := approachPoint d i.val

theorem approachPos_injective (d alpha : ℕ) : Function.Injective (approachPos d alpha) := by
  intro i j he
  unfold approachPos approachPoint at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hy := congrFun he 1
     have hz := congrFun he 2
     dsimp only [point] at hx hy hz
     apply Fin.ext
     omega)

theorem approachPos_adjacent (d alpha : ℕ) (i j : Fin (alpha+8)) (hij : i.val+1=j.val) :
    cubicLattice.Adj (approachPos d alpha i) (approachPos d alpha j) := by
  change latticeDistance (approachPoint _ _) (approachPoint _ _) = 1
  unfold approachPoint
  split_ifs <;> try omega
  all_goals rw [distance_eq]; dsimp only [point]; omega

def approachFold (d alpha : ℕ) : Fold cubicLattice (alpha+8) where
  pos := approachPos d alpha
  injective_pos := approachPos_injective d alpha
  consecutive := approachPos_adjacent d alpha

theorem approachPos_first (d alpha : ℕ) (i : Fin (alpha+8)) (hi : i.val=0) :
    approachPos d alpha i = point d ((d : ℤ)+2) 1 := by
  simp [approachPos, approachPoint, hi]

theorem approachPos_last (d alpha : ℕ) (i : Fin (alpha+8)) (hi : i.val+1=alpha+8) :
    approachPos d alpha i = point ((d : ℤ)+1) ((d : ℤ)+1-alpha) (-2) := by
  have h0 : ¬ i.val<2 := by omega
  have h1 : ¬ i.val<5 := by omega
  have h2 : ¬ i.val<6 := by omega
  apply site_ext <;> simp only [approachPos, approachPoint, if_neg h0, if_neg h1, if_neg h2, point] <;> omega

theorem approachPos_exterior (d alpha : ℕ) (i : Fin (alpha+8)) :
    (d : ℤ)+1 < approachPos d alpha i 1 ∨ approachPos d alpha i 2 = -2 := by
  unfold approachPos approachPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem approachPos_above_or_outer (d alpha : ℕ) (i : Fin (alpha+8)) :
    (d : ℤ)+1 < approachPos d alpha i 1 ∨
      (approachPos d alpha i 0 = (d : ℤ)+1 ∧ approachPos d alpha i 2 = -2) := by
  unfold approachPos approachPoint
  split_ifs <;> dsimp only [point] <;> omega

theorem approachPos_not_mem_cube (d alpha : ℕ) (i : Fin (alpha+8)) :
    approachPos d alpha i ∉ cube (fun _ => 0) (d+2) := by
  intro hp
  have hy := hp 1
  have hz := hp 2
  have he := approachPos_exterior d alpha i
  dsimp only at hy hz
  omega

theorem bulkFold_in_cube (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (d^3+2)) : (bulkFold d hd heven).pos i ∈ cube (fun _ => 0) (d+2) := by
  have hs := (bulkFold_sites d hd heven _).mp ⟨i, rfl⟩
  rcases hs with hp | hp | hp
  · rw [hp]
    intro k
    fin_cases k <;> simp [upperHole, point] <;> omega
  · intro k
    have hk := hp k
    dsimp only at hk ⊢
    omega
  · rw [hp]
    intro k
    fin_cases k <;> simp [lowerHole, point] <;> omega

theorem initial_bulk_seam (d : ℕ) :
    cubicLattice.Adj (point d ((d : ℤ)+2) d) (upperHole d) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [upperHole, point]

theorem approach_wall_seam (d alpha : ℕ) (i : Fin (alpha+8)) (hi : i.val+1=alpha+8) :
    cubicLattice.Adj (approachPos d alpha i) (point ((d : ℤ)+1) ((d : ℤ)+1-alpha) (-1)) := by
  rw [approachPos_last d alpha i hi]
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [point]

theorem bulk_approach_disjoint (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    ∀ i j, (bulkFold d hd heven).pos i ≠ (approachFold d alpha).pos j := by
  intro i j he
  have hb : (bulkFold d hd heven).pos i 1 ≤ (d : ℤ)+1 ∧
      1 ≤ (bulkFold d hd heven).pos i 2 := by
    have hs := (bulkFold_sites d hd heven ((bulkFold d hd heven).pos i)).mp ⟨i, rfl⟩
    rcases hs with hp | hp | hp
    · rw [hp]; simp [upperHole, point]; omega
    · have hy := hp 1; have hz := hp 2
      dsimp only at hy hz
      omega
    · rw [hp]; simp [lowerHole, point]
  have ha := approachPos_exterior d alpha j
  have hy := congrFun he 1
  have hz := congrFun he 2
  change (bulkFold d hd heven).pos i 1 = approachPos d alpha j 1 at hy
  change (bulkFold d hd heven).pos i 2 = approachPos d alpha j 2 at hz
  omega

theorem bulk_approach_seam (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    ∀ i : Fin (d^3+2), ∀ j : Fin (alpha+8),
      i.val+1=d^3+2 → j.val=0 →
      cubicLattice.Adj ((bulkFold d hd heven).pos i) ((approachFold d alpha).pos j) := by
  intro i j hi hj
  rw [bulkFold_last d hd heven i hi]
  change latticeDistance (lowerHole d) (approachPos d alpha j) = 1
  rw [approachPos_first d alpha j hj, distance_eq]
  simp [lowerHole, point]

def bulkApproachFold (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    Fold cubicLattice (d^3+2+(alpha+8)) :=
  Fold.append (bulkFold d hd heven) (approachFold d alpha)
    (bulk_approach_disjoint d alpha hd heven) (bulk_approach_seam d alpha hd heven)

theorem bulkApproachFold_first (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (d^3+2+(alpha+8))) (hi : i.val=0) :
    (bulkApproachFold d alpha hd heven).pos i = upperHole d := by
  cases i using Fin.addCases with
  | left i =>
    simp only [bulkApproachFold, Fold.append_pos_left]
    exact bulkFold_first d hd heven i hi
  | right i => change d^3+2+i.val=0 at hi; omega

theorem bulkApproachFold_last (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (d^3+2+(alpha+8))) (hi : i.val+1=d^3+2+(alpha+8)) :
    (bulkApproachFold d alpha hd heven).pos i = point ((d : ℤ)+1) ((d : ℤ)+1-alpha) (-2) := by
  cases i using Fin.addCases with
  | left i => have := i.isLt; change i.val+1=d^3+2+(alpha+8) at hi; omega
  | right i =>
    simp only [bulkApproachFold, Fold.append_pos_right]
    apply approachPos_last
    change d^3+2+i.val+1=d^3+2+(alpha+8) at hi
    omega

def bulkWord (d : ℕ) : Sequence := List.replicate (d^3+2) .H
def approachWord (alpha : ℕ) : Sequence := List.replicate (alpha+8) .P
def bulkApproachWord (d alpha : ℕ) : Sequence := bulkWord d ++ approachWord alpha

def bulkWordFold (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    Fold cubicLattice (bulkWord d).length := (bulkFold d hd heven).onLength (by simp [bulkWord])

def approachWordFold (d alpha : ℕ) : Fold cubicLattice (approachWord alpha).length :=
  (approachFold d alpha).onLength (by simp [approachWord])

def bulkApproachWordFold (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    Fold cubicLattice (bulkApproachWord d alpha).length :=
  Fold.appendWord (bulkWordFold d hd heven) (approachWordFold d alpha)
    (fun i j => bulk_approach_disjoint d alpha hd heven _ _)
    (fun i j hi hj => bulk_approach_seam d alpha hd heven _ _
      (by simpa only [bulkWord, List.length_replicate] using hi) hj)

/-- Exactly the interior and the two missing top-face sites are hydrophobic;
the exterior approach adds no H sites. -/
theorem bulkApproachWord_hydrophobicSites (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) :
    hydrophobicSites (bulkApproachWord d alpha) (bulkApproachWordFold d alpha hd heven) =
      {p | p = upperHole d ∨ p ∈ cube (fun _ => 1) d ∨ p = lowerHole d} := by
  ext p
  change (∃ i, (bulkWord d ++ approachWord alpha).get i = .H ∧
    (Fold.appendWord _ _ _ _).pos i = p) ↔ _
  rw [Fold.appendWord_exists_residue]
  have hPH : Residue.P ≠ Residue.H := by decide
  simp only [bulkWord, approachWord, List.get_eq_getElem, List.getElem_replicate,
    true_and, hPH, false_and, exists_false, or_false]
  rw [bulkWordFold, onLength_sites]
  exact bulkFold_sites d hd heven p

theorem bulkApproachWordFold_first (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (bulkApproachWord d alpha).length) (hi : i.val=0) :
    (bulkApproachWordFold d alpha hd heven).pos i = upperHole d := by
  let j : Fin (bulkWord d).length := ⟨0, by simp [bulkWord]⟩
  have he : i = Fold.leftWordIndex (bulkWord d) (approachWord alpha) j := Fin.ext hi
  rw [he]
  simp only [bulkApproachWordFold, Fold.appendWord_pos_left]
  change (bulkFold d hd heven).pos (Fin.cast _ j) = _
  exact bulkFold_first d hd heven _ rfl

theorem bulkApproachWordFold_last (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (bulkApproachWord d alpha).length) (hi : i.val+1=(bulkApproachWord d alpha).length) :
    (bulkApproachWordFold d alpha hd heven).pos i = point ((d : ℤ)+1) ((d : ℤ)+1-alpha) (-2) := by
  let j : Fin (approachWord alpha).length := ⟨alpha+7, by simp [approachWord]⟩
  have he : i = Fold.rightWordIndex (bulkWord d) (approachWord alpha) j := by
    apply Fin.ext
    change i.val = (bulkWord d).length + (alpha+7)
    simp only [bulkApproachWord, bulkWord, approachWord, List.length_append, List.length_replicate] at hi ⊢
    omega
  rw [he]
  simp only [bulkApproachWordFold, Fold.appendWord_pos_right]
  change approachPos d alpha (Fin.cast _ j) = _
  apply approachPos_last
  change alpha+7+1=alpha+8
  omega

end ProteinFolding.CubicPackingBulk
