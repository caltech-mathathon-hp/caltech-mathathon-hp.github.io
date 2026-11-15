import ProteinFolding.Common.FoldConcatenation
import ProteinFolding.Cubic.Proofs.PackingGeometryLocal
import ProteinFolding.Cubic.Proofs.PackingEdgeNormals

/-! The explicit compressed path of the initial E_(9d+8) block: two opposite
square perimeters, traversed in opposite orders, joined by one cube edge.
The path starts and ends one lattice step before the joining corners. -/

namespace ProteinFolding.CubicPackingPrefix

open CubicCertificates CubicPackingGeometry

def squareX (L i : ℕ) : ℤ :=
  if i < L then (L : ℤ) - 1 - i
  else if i < 2 * L then 0
  else if i < 3 * L then (i : ℤ) + 1 - 2 * L
  else L

def squareZ (L i : ℕ) : ℤ :=
  if i < L then L
  else if i < 2 * L then (2 * L : ℤ) - 1 - i
  else if i < 3 * L then 0
  else (i : ℤ) + 1 - 3 * L

def perimeterPos (L y : ℕ) (i : Fin (4 * L)) : Site
  | 0 => squareX L i.val
  | 1 => y
  | 2 => squareZ L i.val

theorem perimeterPos_injective (L y : ℕ) : Function.Injective (perimeterPos L y) := by
  intro i j he
  have hx := congrFun he 0
  have hz := congrFun he 2
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  dsimp [perimeterPos, squareX, squareZ] at hx hz
  split_ifs at hx hz <;> omega

theorem square_bounds (L : ℕ) (i : Fin (4 * L)) :
    0 ≤ squareX L i.val ∧ squareX L i.val ≤ L ∧
    0 ≤ squareZ L i.val ∧ squareZ L i.val ≤ L := by
  have hi := i.isLt
  dsimp [squareX, squareZ]
  split_ifs <;> omega

theorem square_boundary (L : ℕ) (i : Fin (4 * L)) :
    squareX L i.val = 0 ∨ squareX L i.val = L ∨
      squareZ L i.val = 0 ∨ squareZ L i.val = L := by
  dsimp [squareX, squareZ]
  split_ifs <;> omega

theorem square_step (L : ℕ) (i j : Fin (4 * L)) (hij : i.val + 1 = j.val) :
    (squareX L i.val - squareX L j.val = 1 ∧ squareZ L i.val = squareZ L j.val) ∨
    (squareX L i.val - squareX L j.val = -1 ∧ squareZ L i.val = squareZ L j.val) ∨
    (squareX L i.val = squareX L j.val ∧ squareZ L i.val - squareZ L j.val = 1) ∨
    (squareX L i.val = squareX L j.val ∧ squareZ L i.val - squareZ L j.val = -1) := by
  have hi := i.isLt
  have hj := j.isLt
  dsimp [squareX, squareZ]
  split_ifs <;> omega

theorem perimeterPos_adjacent (L y : ℕ) (i j : Fin (4 * L)) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (perimeterPos L y i) (perimeterPos L y j) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  rcases square_step L i j hij with h | h | h | h <;>
    simp only [perimeterPos, h.1, h.2, sub_self, Int.natAbs_one, Int.natAbs_neg,
      Int.natAbs_zero, Nat.zero_add, Nat.add_zero]

/-- All 4L sites of one square perimeter in their explicit traversal order. -/
def perimeterFold (L y : ℕ) : Fold cubicLattice (4 * L) where
  pos := perimeterPos L y
  injective_pos := perimeterPos_injective L y
  consecutive := fun i j hij => perimeterPos_adjacent L y i j hij

theorem perimeterPos_first (L y : ℕ) (hL : 0 < L) :
    perimeterPos L y ⟨0, by omega⟩ =
      fun k => if k = 0 then (L : ℤ) - 1 else if k = 1 then y else L := by
  apply site_ext <;> simp [perimeterPos, squareX, squareZ, hL]

theorem perimeterPos_last (L y : ℕ) (hL : 0 < L) :
    perimeterPos L y ⟨4 * L - 1, by omega⟩ =
      fun k => if k = 1 then (y : ℤ) else L := by
  apply site_ext <;> simp only [perimeterPos, squareX, squareZ]
  all_goals split_ifs <;> omega

def bridgePos (d : ℕ) (i : Fin d) : Site
  | 0 => (d : ℤ) + 1
  | 1 => (d : ℤ) - i.val
  | 2 => (d : ℤ) + 1

def bridgeFold (d : ℕ) : Fold cubicLattice d where
  pos := bridgePos d
  injective_pos := by
    intro i j he
    have hy := congrFun he 1
    apply Fin.ext
    dsimp [bridgePos] at hy
    omega
  consecutive := by
    intro i j hij
    change latticeDistance _ _ = 1
    rw [distance_eq]
    have hy : bridgePos d i 1 - bridgePos d j 1 = 1 := by dsimp [bridgePos]; omega
    rw [hy]
    simp [bridgePos]

theorem upper_bridge_disjoint (d : ℕ) :
    ∀ i j, (perimeterFold (d + 1) (d + 1)).pos i ≠ (bridgeFold d).pos j := by
  intro i j he
  have hy := congrFun he 1
  change ((d + 1 : ℕ) : ℤ) = (d : ℤ) - j.val at hy
  omega

theorem upper_bridge_seam (d : ℕ) :
    ∀ i : Fin (4 * (d + 1)), ∀ j : Fin d,
      i.val + 1 = 4 * (d + 1) → j.val = 0 →
      cubicLattice.Adj ((perimeterFold (d + 1) (d + 1)).pos i) ((bridgeFold d).pos j) := by
  intro i j hi hj
  have he : i = ⟨4 * (d + 1) - 1, by omega⟩ := by
    apply Fin.ext
    change i.val = 4 * (d + 1) - 1
    omega
  change latticeDistance (perimeterPos (d + 1) (d + 1) i) (bridgePos d j) = 1
  rw [he, perimeterPos_last (d + 1) (d + 1) (by omega), distance_eq]
  have hy : ((d + 1 : ℕ) : ℤ) - ((d : ℤ) - j.val) = 1 := by omega
  change _ + (((d + 1 : ℕ) : ℤ) - ((d : ℤ) - j.val)).natAbs + _ = 1
  rw [hy]
  simp [bridgePos]

def upperBridgeFold (d : ℕ) : Fold cubicLattice (4 * (d + 1) + d) :=
  Fold.append (perimeterFold (d + 1) (d + 1)) (bridgeFold d)
    (upper_bridge_disjoint d) (upper_bridge_seam d)

theorem upperBridge_lower_disjoint (d : ℕ) :
    ∀ i j, (upperBridgeFold d).pos i ≠ ((perimeterFold (d + 1) 0).reverse).pos j := by
  intro i j he
  have hy := congrFun he 1
  cases i using Fin.addCases with
  | left i =>
    simp only [upperBridgeFold, Fold.append_pos_left] at hy
    change ((d + 1 : ℕ) : ℤ) = 0 at hy
    omega
  | right i =>
    have hi := i.isLt
    simp only [upperBridgeFold, Fold.append_pos_right] at hy
    change (d : ℤ) - i.val = 0 at hy
    omega

theorem upperBridge_lower_seam (d : ℕ) (hd : 0 < d) :
    ∀ i : Fin (4 * (d + 1) + d), ∀ j : Fin (4 * (d + 1)),
      i.val + 1 = 4 * (d + 1) + d → j.val = 0 →
      cubicLattice.Adj ((upperBridgeFold d).pos i) ((perimeterFold (d + 1) 0).reverse.pos j) := by
  intro i j hi hj
  cases i using Fin.addCases with
  | left i =>
    have hil := i.isLt
    change i.val + 1 = 4 * (d + 1) + d at hi
    omega
  | right i =>
    have hi' : i.val + 1 = d := by change 4 * (d + 1) + i.val + 1 = _ at hi; omega
    have hj' : j.rev = ⟨4 * (d + 1) - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, hj]
    simp only [upperBridgeFold, Fold.append_pos_right]
    change latticeDistance (bridgePos d i) (perimeterPos (d + 1) 0 j.rev) = 1
    rw [hj', perimeterPos_last (d + 1) 0 (by omega), distance_eq]
    have hy : (d : ℤ) - i.val = 1 := by omega
    change _ + (((d : ℤ) - i.val) - 0).natAbs + _ = 1
    rw [sub_zero, hy]
    simp [bridgePos]

/-- The 9d+8 distinct skeleton sites traversed by the initial compressed E block. -/
def skeletonPrefixFold (d : ℕ) (hd : 0 < d) : Fold cubicLattice (9 * d + 8) :=
  (Fold.append (upperBridgeFold d) (perimeterFold (d + 1) 0).reverse
    (upperBridge_lower_disjoint d) (upperBridge_lower_seam d hd)).onLength (by omega)

theorem perimeterPos_skeleton (L y : ℕ) (hy : y = 0 ∨ y = L) (i : Fin (4 * L)) :
    EdgeSkeleton (fun _ => 0) (L + 1) (perimeterPos L y i) := by
  have hb := square_bounds L i
  have hyl : 0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ L := by rcases hy with hy | hy <;> omega
  refine ⟨?_, ?_⟩
  · rw [cube_mem_coordinates]
    dsimp [perimeterPos]
    omega
  · have hyb : BoundaryCoordinate (fun _ => 0) (perimeterPos L y i) (L + 1) 1 := by
      dsimp [BoundaryCoordinate, perimeterPos]
      rcases hy with hy | hy <;> omega
    rcases square_boundary L i with hx | hx | hz | hz
    · exact ⟨1, 0, by decide, hyb, Or.inl hx⟩
    · refine ⟨1, 0, by decide, hyb, Or.inr ?_⟩
      change squareX L i.val + 1 = 0 + ((L + 1 : ℕ) : ℤ)
      omega
    · exact ⟨1, 2, by decide, hyb, Or.inl hz⟩
    · refine ⟨1, 2, by decide, hyb, Or.inr ?_⟩
      change squareZ L i.val + 1 = 0 + ((L + 1 : ℕ) : ℤ)
      omega

theorem bridgePos_skeleton (d : ℕ) (i : Fin d) :
    EdgeSkeleton (fun _ => 0) (d + 2) (bridgePos d i) := by
  have hi := i.isLt
  refine ⟨?_, 0, 2, by decide, Or.inr ?_, Or.inr ?_⟩
  · rw [cube_mem_coordinates]
    dsimp [bridgePos]
    omega
  · change (d : ℤ) + 1 + 1 = 0 + ((d + 2 : ℕ) : ℤ)
    omega
  · change (d : ℤ) + 1 + 1 = 0 + ((d + 2 : ℕ) : ℤ)
    omega

theorem skeletonPrefixFold_skeleton (d : ℕ) (hd : 0 < d) (i : Fin (9 * d + 8)) :
    EdgeSkeleton (fun _ => 0) (d + 2) ((skeletonPrefixFold d hd).pos i) := by
  change EdgeSkeleton _ _ ((Fold.append (upperBridgeFold d) (perimeterFold (d + 1) 0).reverse
    (upperBridge_lower_disjoint d) (upperBridge_lower_seam d hd)).pos
      (Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1)) i))
  generalize Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1)) i = j
  cases j using Fin.addCases with
  | left j =>
    simp only [Fold.append_pos_left]
    cases j using Fin.addCases with
    | left j =>
      simp only [upperBridgeFold, Fold.append_pos_left]
      exact perimeterPos_skeleton (d + 1) (d + 1) (Or.inr rfl) j
    | right j =>
      simp only [upperBridgeFold, Fold.append_pos_right]
      exact bridgePos_skeleton d j
  | right j =>
    simp only [Fold.append_pos_right]
    exact perimeterPos_skeleton (d + 1) 0 (Or.inl rfl) j.rev

theorem skeletonPrefixFold_coordinate_cases (d : ℕ) (hd : 0 < d) (i : Fin (9 * d + 8)) :
    ((skeletonPrefixFold d hd).pos i 1 = 0 ∨ (skeletonPrefixFold d hd).pos i 1 = (d : ℤ) + 1) ∨
      ((skeletonPrefixFold d hd).pos i 0 = (d : ℤ) + 1 ∧
        (skeletonPrefixFold d hd).pos i 2 = (d : ℤ) + 1) := by
  simp only [skeletonPrefixFold, Fold.onLength]
  generalize Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1)) i = j
  cases j using Fin.addCases with
  | left j =>
    simp only [Fold.append_pos_left]
    cases j using Fin.addCases with
    | left j =>
      left
      right
      simp [upperBridgeFold, perimeterFold, perimeterPos]
    | right j =>
      right
      simp [upperBridgeFold, bridgeFold, bridgePos]
  | right j =>
    left
    left
    rw [Fold.append_pos_right]
    rfl

theorem skeletonPrefixFold_avoids_back_edge (d : ℕ) (hd : 0 < d)
    (i : Fin (9 * d + 8)) (y : ℤ) (hy0 : 0 < y) (hyd : y ≤ d) :
    (skeletonPrefixFold d hd).pos i ≠
      fun k => if k = 0 then 0 else if k = 1 then y else (d : ℤ) + 1 := by
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  rcases skeletonPrefixFold_coordinate_cases d hd i with h | h
  · rcases h with h | h <;> simp only [↓reduceIte] at hx hy <;> omega
  · simp only [↓reduceIte] at hx hy
    omega

theorem skeletonPrefixFold_first (d : ℕ) (hd : 0 < d) :
    (skeletonPrefixFold d hd).pos ⟨0, by omega⟩ =
      fun k => if k = 0 then (d : ℤ) else (d : ℤ) + 1 := by
  change (Fold.append (upperBridgeFold d) (perimeterFold (d + 1) 0).reverse
    (upperBridge_lower_disjoint d) (upperBridge_lower_seam d hd)).pos
    (Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1)) ⟨0, by omega⟩) = _
  have hi : Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1))
      (⟨0, by omega⟩ : Fin (9 * d + 8)) =
      Fin.castAdd (4 * (d + 1)) (Fin.castAdd d (⟨0, by omega⟩ : Fin (4 * (d + 1)))) := Fin.ext rfl
  rw [hi, Fold.append_pos_left]
  simp only [upperBridgeFold, Fold.append_pos_left]
  change perimeterPos (d + 1) (d + 1) ⟨0, by omega⟩ = _
  rw [perimeterPos_first (d + 1) (d + 1) (by omega)]
  apply site_ext <;> simp

theorem skeletonPrefixFold_last (d : ℕ) (hd : 0 < d) :
    (skeletonPrefixFold d hd).pos ⟨9 * d + 8 - 1, by omega⟩ =
      fun k => if k = 0 then (d : ℤ) else if k = 1 then 0 else (d : ℤ) + 1 := by
  change (Fold.append (upperBridgeFold d) (perimeterFold (d + 1) 0).reverse
    (upperBridge_lower_disjoint d) (upperBridge_lower_seam d hd)).pos
    (Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1)) ⟨9 * d + 8 - 1, by omega⟩) = _
  have hi : Fin.cast (by omega : 9 * d + 8 = 4 * (d + 1) + d + 4 * (d + 1))
      (⟨9 * d + 8 - 1, by omega⟩ : Fin (9 * d + 8)) =
      Fin.natAdd (4 * (d + 1) + d) (⟨4 * (d + 1) - 1, by omega⟩ : Fin (4 * (d + 1))) := by
    apply Fin.ext
    change 9 * d + 8 - 1 = 4 * (d + 1) + d + (4 * (d + 1) - 1)
    omega
  rw [hi, Fold.append_pos_right]
  change perimeterPos (d + 1) 0 (Fin.rev ⟨4 * (d + 1) - 1, by omega⟩) = _
  have hr : Fin.rev (⟨4 * (d + 1) - 1, by omega⟩ : Fin (4 * (d + 1))) = ⟨0, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [hr, perimeterPos_first (d + 1) 0 (by omega)]
  apply site_ext <;> simp

/-- The entire initial literal E block has a valid fold with a prescribed
final P pointing out of the lower-y face. No attachment hypothesis remains. -/
theorem skeletonPrefix_edgeWord_lift_exists (d : ℕ) (hd : 0 < d) :
    ∃ lifted : Fold cubicLattice (CubicPacking.edgeWord (9 * d + 8)).length,
      hydrophobicSites (CubicPacking.edgeWord (9 * d + 8)) lifted =
        Set.range (skeletonPrefixFold d hd).pos ∧
      (∀ i, (CubicPacking.edgeWord (9 * d + 8)).get i = .P →
        lifted.pos i ∉ cube (fun _ => 0) (d + 2)) ∧
      lifted.pos (CubicPackingLift.edgeLastIndex (9 * d + 8) (by omega)) =
        fun k => if k = 0 then (d : ℤ) else if k = 1 then -1 else (d : ℤ) + 1 := by
  have hout : step ((skeletonPrefixFold d hd).pos ⟨9 * d + 8 - 1, by omega⟩) 3 ∉
      cube (fun _ => 0) (d + 2) := by
    intro hm
    have hy := (hm 1).1
    rw [skeletonPrefixFold_last] at hy
    simp [step] at hy
  obtain ⟨lifted, hH, hP, hlast⟩ := CubicPackingLift.edgeWord_lift_exists
    (9 * d + 8) (by omega) (skeletonPrefixFold d hd) (fun _ => 0) (d + 2)
    (skeletonPrefixFold_skeleton d hd) 3 hout
  refine ⟨lifted, hH, hP, ?_⟩
  rw [hlast, skeletonPrefixFold_last]
  apply site_ext <;> simp [step]

/-- The terminal normal used by the complete prefix: its final P points in
the positive z direction and joins the first P of the back-face F block. -/
theorem skeletonPrefix_edgeWord_back_lift_exists (d : ℕ) (hd : 0 < d) :
    ∃ lifted : Fold cubicLattice (CubicPacking.edgeWord (9 * d + 8)).length,
      hydrophobicSites (CubicPacking.edgeWord (9 * d + 8)) lifted =
        Set.range (skeletonPrefixFold d hd).pos ∧
      (∀ i, (CubicPacking.edgeWord (9 * d + 8)).get i = .P →
        lifted.pos i ∉ cube (fun _ => 0) (d + 2)) ∧
      lifted.pos (CubicPackingLift.edgeLastIndex (9 * d + 8) (by omega)) =
        fun k => if k = 0 then (d : ℤ) else if k = 1 then 0 else (d : ℤ) + 2 := by
  have hout : step ((skeletonPrefixFold d hd).pos ⟨9 * d + 8 - 1, by omega⟩) 4 ∉
      cube (fun _ => 0) (d + 2) := by
    intro hm
    have hz := (hm 2).2
    rw [skeletonPrefixFold_last] at hz
    simp [step] at hz
    omega
  obtain ⟨lifted, hH, hP, hlast⟩ := CubicPackingLift.edgeWord_lift_exists
    (9 * d + 8) (by omega) (skeletonPrefixFold d hd) (fun _ => 0) (d + 2)
    (skeletonPrefixFold_skeleton d hd) 4 hout
  refine ⟨lifted, hH, hP, ?_⟩
  rw [hlast, skeletonPrefixFold_last]
  apply site_ext <;> simp [step] <;> omega

end ProteinFolding.CubicPackingPrefix
