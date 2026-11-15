import ProteinFolding.Cubic.Proofs.PackingFaceLift
import ProteinFolding.Common.FoldConcatenation

/-! The literal top-face `F_(d²−2)` completeness component. It traverses
the reversed square snake after deleting its two endpoint cells. The missing
cells are `(d,d+1,d)` and `(d,d+1,1)`, which belong to the following bulk.
The outward P layer has y-coordinate `d+2`. -/

namespace ProteinFolding.CubicPackingTopFace

open CubicCertificates CubicPacking CubicPackingSnake CubicPackingLift

def point (x y z : ℤ) : Site
  | 0 => x
  | 1 => y
  | 2 => z

def topMap (d : ℕ) (p : Site) : Site := point (d - p 0) (d + 1 - p 2) (d - p 1)

theorem topMap_injective (d : ℕ) : Function.Injective (topMap d) := by
  intro p q he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  apply site_ext <;> dsimp [topMap, point] at hx hy hz <;> omega

theorem topMap_adj (d : ℕ) (p q : Site) (ha : cubicLattice.Adj p q) :
    cubicLattice.Adj (topMap d p) (topMap d q) := by
  change latticeDistance _ _ = 1 at ha ⊢
  rw [distance_eq] at ha ⊢
  have hx : (d : ℤ) - p 0 - ((d : ℤ) - q 0) = -(p 0 - q 0) := by ring
  have hy : (d : ℤ) - p 1 - ((d : ℤ) - q 1) = -(p 1 - q 1) := by ring
  have hz : (d : ℤ) + 1 - p 2 - ((d : ℤ) + 1 - q 2) = -(p 2 - q 2) := by ring
  simpa only [topMap, point, hx, hy, hz, Int.natAbs_neg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ha

def trimIndex (d : ℕ) (hd : 2 ≤ d) (i : Fin (d * d - 2)) : Fin (d * d) :=
  ⟨i.val + 1, by
    have hi := i.isLt
    have hn : 4 ≤ d * d := by nlinarith
    omega⟩

def trimFold (d : ℕ) (hd : 2 ≤ d) : Fold cubicLattice (d * d - 2) where
  pos i := rectanglePos d d (trimIndex d hd i)
  injective_pos := by
    intro i j he
    have h := congrArg Fin.val (rectanglePos_injective d d he)
    change i.val + 1 = j.val + 1 at h
    exact Fin.ext (by omega)
  consecutive i j hij := rectanglePos_adjacent d d (by omega) _ _ (by
    change i.val + 1 + 1 = j.val + 1
    omega)

def baseFold (d : ℕ) (hd : 2 ≤ d) : Fold cubicLattice (d * d - 2) := (trimFold d hd).reverse

theorem baseFold_plane (d : ℕ) (hd : 2 ≤ d) (i : Fin (d * d - 2)) :
    (baseFold d hd).pos i 2 = 0 := rfl

theorem topLength_even (d : ℕ) (heven : d % 2 = 0) : 2 ∣ d * d - 2 := by
  have hd : 2 ∣ d := Nat.dvd_of_mod_eq_zero heven
  exact Nat.dvd_sub (dvd_mul_of_dvd_left hd d) (by decide)

/-- Explicit self-avoiding fold for the original literal face word. -/
def topFold (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    Fold cubicLattice (faceWord (d * d - 2)).length where
  pos i := topMap d ((faceLift _ (topLength_even d heven) (baseFold d hd) (baseFold_plane d hd)).pos i)
  injective_pos := (topMap_injective d).comp
    (faceLift _ (topLength_even d heven) (baseFold d hd) (baseFold_plane d hd)).injective_pos
  consecutive i j hij := topMap_adj d _ _
    ((faceLift _ (topLength_even d heven) (baseFold d hd) (baseFold_plane d hd)).consecutive i j hij)

theorem rectanglePos_bounds (d : ℕ) (i : Fin (d * d)) :
    0 ≤ rectanglePos d d i 0 ∧ rectanglePos d d i 0 < (d : ℤ) ∧
      0 ≤ rectanglePos d d i 1 ∧ rectanglePos d d i 1 < (d : ℤ) := by
  have hx := (rectangleCells d d i).2.isLt
  have hy := (rectangleCells d d i).1.isLt
  change 0 ≤ ((rectangleCells d d i).2.val : ℤ) ∧ ((rectangleCells d d i).2.val : ℤ) < d ∧
    0 ≤ ((rectangleCells d d i).1.val : ℤ) ∧ ((rectangleCells d d i).1.val : ℤ) < d
  omega

theorem rectanglePos_exists (d : ℕ) (p : Site)
    (hx : 0 ≤ p 0 ∧ p 0 < (d : ℤ)) (hy : 0 ≤ p 1 ∧ p 1 < (d : ℤ)) (hz : p 2 = 0) :
    ∃ i : Fin (d * d), rectanglePos d d i = p := by
  let cell : Fin d × Fin d := (⟨(p 1).toNat, by omega⟩, ⟨(p 0).toNat, by omega⟩)
  refine ⟨(rectangleCells d d).symm cell, ?_⟩
  unfold rectanglePos
  rw [Equiv.apply_symm_apply]
  apply site_ext <;> dsimp [gridPoint, cell] <;> omega

theorem baseFold_range (d : ℕ) (hd : 2 ≤ d) (p : Site) :
    (∃ i, (baseFold d hd).pos i = p) ↔
      ∃ j : Fin (d * d), rectanglePos d d j = p ∧ 0 < j.val ∧ j.val + 1 < d * d := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨trimIndex d hd i.rev, hi, ?_, ?_⟩
    · change 0 < i.rev.val + 1; omega
    · change i.rev.val + 1 + 1 < d * d
      have := i.rev.isLt
      have : 4 ≤ d * d := by nlinarith
      omega
  · rintro ⟨j, hj, hpos, hlast⟩
    let i : Fin (d * d - 2) := ⟨j.val - 1, by omega⟩
    refine ⟨i.rev, ?_⟩
    have he : trimIndex d hd i = j := by apply Fin.ext; dsimp [trimIndex, i]; omega
    change rectanglePos d d (trimIndex d hd i.rev.rev) = p
    simpa only [Fin.rev_rev, he] using hj

theorem topLength_pos (d : ℕ) (hd : 2 ≤ d) : 0 < d * d - 2 := by
  have : 4 ≤ d * d := by nlinarith
  omega

theorem penultimate_divmod (d : ℕ) (hd : 2 ≤ d) :
    (d * d - 2) / d = d - 1 ∧ (d * d - 2) % d = d - 2 := by
  have hd0 : 0 < d := by omega
  have hsub1 : d - 1 + 1 = d := by omega
  have hsub2 : d - 2 + 2 = d := by omega
  have hsquare : 4 ≤ d * d := by nlinarith
  have hsquare_sub : d * d - 2 + 2 = d * d := by omega
  have hsplit : d * d - 2 = d - 2 + d * (d - 1) := by nlinarith
  have hlt : d - 2 < d := by omega
  rw [hsplit, Nat.add_mul_div_left _ _ hd0, Nat.div_eq_of_lt hlt,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  exact ⟨rfl, rfl⟩

theorem rectanglePos_second (d : ℕ) (hd : 2 ≤ d) :
    rectanglePos d d ⟨1, by nlinarith⟩ = point 1 0 0 := by
  have hlt : 1 < d := by omega
  apply site_ext
  · rw [rectanglePos_x]
    simp [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, point]
  · rw [rectanglePos_y]
    simp [Nat.div_eq_of_lt hlt, point]
  · rfl

theorem rectanglePos_penultimate (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    rectanglePos d d ⟨d * d - 2, by have := topLength_pos d hd; omega⟩ = point 1 (d - 1) 0 := by
  obtain ⟨hdiv, hmod⟩ := penultimate_divmod d hd
  have hp : (d - 1) % 2 ≠ 0 := by omega
  apply site_ext
  · rw [rectanglePos_x, hdiv, hmod, if_neg hp]
    dsimp [point]
    omega
  · rw [rectanglePos_y, hdiv]
    dsimp [point]
    omega
  · rfl

theorem baseFold_first (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    (baseFold d hd).pos ⟨0, topLength_pos d hd⟩ = point 1 (d - 1) 0 := by
  have hsquare : 4 ≤ d * d := by nlinarith
  have hi : trimIndex d hd (⟨0, topLength_pos d hd⟩ : Fin (d * d - 2)).rev =
      (⟨d * d - 2, by omega⟩ : Fin (d * d)) := by
    apply Fin.ext
    simp only [trimIndex, Fin.val_rev]
    omega
  change rectanglePos d d _ = _
  rw [hi]
  exact rectanglePos_penultimate d hd heven

theorem baseFold_last (d : ℕ) (hd : 2 ≤ d) :
    (baseFold d hd).pos ⟨d * d - 2 - 1, by have := topLength_pos d hd; omega⟩ = point 1 0 0 := by
  have hsquare : 4 ≤ d * d := by nlinarith
  have hi : trimIndex d hd (⟨d * d - 2 - 1, by have := topLength_pos d hd; omega⟩ :
      Fin (d * d - 2)).rev = (⟨1, by nlinarith⟩ : Fin (d * d)) := by
    apply Fin.ext
    simp only [trimIndex, Fin.val_rev]
    omega
  change rectanglePos d d _ = _
  rw [hi]
  exact rectanglePos_second d hd

theorem topFold_first (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    (topFold d hd heven).pos
      (faceFirstIndex (d * d - 2) (topLength_even d heven) (topLength_pos d hd)) =
      point (d - 1) (d + 2) 1 := by
  change topMap d (faceLiftPos (d * d - 2) (topLength_even d heven) (baseFold d hd)
    (faceFirstIndex (d * d - 2) (topLength_even d heven) (topLength_pos d hd))) = _
  rw [faceLiftPos_first, baseFold_first d hd heven]
  apply site_ext <;> dsimp [topMap, point, atHeight] <;> omega

theorem topFold_last (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    (topFold d hd heven).pos
      (faceLastIndex (d * d - 2) (topLength_even d heven) (topLength_pos d hd)) =
      point (d - 1) (d + 2) d := by
  change topMap d (faceLiftPos (d * d - 2) (topLength_even d heven) (baseFold d hd)
    (faceLastIndex (d * d - 2) (topLength_even d heven) (topLength_pos d hd))) = _
  rw [faceLiftPos_last, baseFold_last d hd]
  apply site_ext <;> dsimp [topMap, point, atHeight] <;> omega

theorem rectanglePos_corner_first (d : ℕ) (hd : 2 ≤ d) :
    rectanglePos d d ⟨0, by nlinarith⟩ = point 0 0 0 := by
  have he := rectanglePos_first d d (by omega) (by omega)
  change rectanglePos d d ⟨0, _⟩ = _ at he
  rw [he]
  apply site_ext <;> rfl

theorem rectanglePos_corner_last (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    rectanglePos d d ⟨d * d - 1, by have hN := topLength_pos d hd; omega⟩ = point 0 (d - 1) 0 := by
  have he := rectanglePos_last_even d d (by omega) (by omega) heven
  change rectanglePos d d ⟨d * d - 1, _⟩ = _ at he
  rw [he]
  apply site_ext <;> simp [point] <;> omega

theorem baseFold_range_iff (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) (p : Site) :
    (∃ i, (baseFold d hd).pos i = p) ↔
      p 2 = 0 ∧ (0 ≤ p 0 ∧ p 0 < (d : ℤ)) ∧ (0 ≤ p 1 ∧ p 1 < (d : ℤ)) ∧
        p ≠ point 0 0 0 ∧ p ≠ point 0 (d - 1) 0 := by
  rw [baseFold_range]
  constructor
  · rintro ⟨j, rfl, hpos, hlast⟩
    have hb := rectanglePos_bounds d j
    refine ⟨rfl, ⟨hb.1, hb.2.1⟩, hb.2.2, ?_, ?_⟩
    · intro he
      have h := rectanglePos_injective d d (he.trans (rectanglePos_corner_first d hd).symm)
      have hi : j.val = 0 := congrArg Fin.val h
      omega
    · intro he
      have h := rectanglePos_injective d d (he.trans (rectanglePos_corner_last d hd heven).symm)
      have hi : j.val = d * d - 1 := congrArg Fin.val h
      omega
  · rintro ⟨hz, hx, hy, hfirst, hlast⟩
    obtain ⟨j, hj⟩ := rectanglePos_exists d p hx hy hz
    refine ⟨j, hj, ?_, ?_⟩
    · by_contra h
      have he : j = ⟨0, by nlinarith⟩ := by
        apply Fin.ext
        change j.val = 0
        omega
      exact hfirst (hj.symm.trans (he ▸ rectanglePos_corner_first d hd))
    · by_contra h
      have hjlt := j.isLt
      have he : j = ⟨d * d - 1, by have hN := topLength_pos d hd; omega⟩ := by
        apply Fin.ext
        change j.val = d * d - 1
        omega
      exact hlast (hj.symm.trans (he ▸ rectanglePos_corner_last d hd heven))

theorem topFold_hydrophobicSites_range (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) (p : Site) :
    p ∈ hydrophobicSites (faceWord (d * d - 2)) (topFold d hd heven) ↔
      ∃ k, topMap d ((baseFold d hd).pos k) = p := by
  let f := faceLift (d * d - 2) (topLength_even d heven) (baseFold d hd) (baseFold_plane d hd)
  constructor
  · rintro ⟨i, hi, hp⟩
    obtain ⟨k, hk⟩ := (faceLift_hydrophobicSites _ (topLength_even d heven)
      (baseFold d hd) (baseFold_plane d hd) (f.pos i)).mp ⟨i, hi, rfl⟩
    refine ⟨k, ?_⟩
    exact (congrArg (topMap d) hk).trans hp
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi, hp⟩ := (faceLift_hydrophobicSites _ (topLength_even d heven)
      (baseFold d hd) (baseFold_plane d hd) ((baseFold d hd).pos k)).mpr ⟨k, rfl⟩
    exact ⟨i, hi, (congrArg (topMap d) hp).trans hk⟩

def HSupport (d : ℕ) (p : Site) : Prop :=
  p 1 = (d : ℤ) + 1 ∧ (1 ≤ p 0 ∧ p 0 ≤ (d : ℤ)) ∧ (1 ≤ p 2 ∧ p 2 ≤ (d : ℤ)) ∧
    p ≠ point d (d + 1) d ∧ p ≠ point d (d + 1) 1

def inverseTopMap (d : ℕ) (p : Site) : Site := point (d - p 0) (d - p 2) (d + 1 - p 1)

theorem topMap_inverse (d : ℕ) (p : Site) : topMap d (inverseTopMap d p) = p := by
  apply site_ext <;> dsimp [topMap, inverseTopMap, point] <;> omega

theorem topMap_zero (d : ℕ) : topMap d (point 0 0 0) = point d (d + 1) d := by
  apply site_ext <;> simp [topMap, point]

theorem topMap_end (d : ℕ) : topMap d (point 0 (d - 1) 0) = point d (d + 1) 1 := by
  apply site_ext <;> dsimp [topMap, point] <;> omega

/-- Exact H coverage: every interior site of the upper y face, with precisely
the two prescribed bulk terminals omitted. -/
theorem topFold_hydrophobicSites (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) (p : Site) :
    p ∈ hydrophobicSites (faceWord (d * d - 2)) (topFold d hd heven) ↔ HSupport d p := by
  rw [topFold_hydrophobicSites_range]
  constructor
  · rintro ⟨k, rfl⟩
    let b := (baseFold d hd).pos k
    have hb := (baseFold_range_iff d hd heven b).mp ⟨k, rfl⟩
    dsimp only [b] at hb
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp [topMap, point]; omega
    · dsimp [topMap, point]; omega
    · dsimp [topMap, point]; omega
    · intro he
      exact hb.2.2.2.1 (topMap_injective d (he.trans (topMap_zero d).symm))
    · intro he
      exact hb.2.2.2.2 (topMap_injective d (he.trans (topMap_end d).symm))
  · rintro ⟨hy, hx, hz, hfirst, hlast⟩
    let b := inverseTopMap d p
    have hb : b 2 = 0 ∧ (0 ≤ b 0 ∧ b 0 < (d : ℤ)) ∧ (0 ≤ b 1 ∧ b 1 < (d : ℤ)) ∧
        b ≠ point 0 0 0 ∧ b ≠ point 0 (d - 1) 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp [b, inverseTopMap, point]; omega
      · dsimp [b, inverseTopMap, point]; omega
      · dsimp [b, inverseTopMap, point]; omega
      · intro he
        exact hfirst ((topMap_inverse d p).symm.trans ((congrArg (topMap d) he).trans (topMap_zero d)))
      · intro he
        exact hlast ((topMap_inverse d p).symm.trans ((congrArg (topMap d) he).trans (topMap_end d)))
    obtain ⟨k, hk⟩ := (baseFold_range_iff d hd heven b).mpr hb
    exact ⟨k, (congrArg (topMap d) hk).trans (topMap_inverse d p)⟩

/-- Every vertex stays over an interior top-face cell, at H height `d+1`
or exterior P height `d+2`. -/
theorem topFold_bounds (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) :
    (1 ≤ (topFold d hd heven).pos i 0 ∧ (topFold d hd heven).pos i 0 ≤ (d : ℤ)) ∧
    (1 ≤ (topFold d hd heven).pos i 2 ∧ (topFold d hd heven).pos i 2 ≤ (d : ℤ)) ∧
    ((topFold d hd heven).pos i 1 = (d : ℤ) + 1 ∨
      (topFold d hd heven).pos i 1 = (d : ℤ) + 2) := by
  let j := trimIndex d hd (faceBaseIndex (d * d - 2) (topLength_even d heven) i).rev
  have hb := rectanglePos_bounds d j
  change (1 ≤ (d : ℤ) - rectanglePos d d j 0 ∧ (d : ℤ) - rectanglePos d d j 0 ≤ d) ∧
    (1 ≤ (d : ℤ) - rectanglePos d d j 1 ∧ (d : ℤ) - rectanglePos d d j 1 ≤ d) ∧
    ((d : ℤ) + 1 - faceHeight i.val = d + 1 ∨ (d : ℤ) + 1 - faceHeight i.val = d + 2)
  rcases faceHeight_cases i.val with hh | hh <;> rw [hh] <;> omega

theorem topFold_P_height (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (hi : (faceWord (d * d - 2)).get i = .P) :
    (topFold d hd heven).pos i 1 = (d : ℤ) + 2 := by
  have hh := faceLift_P_height (d * d - 2) (topLength_even d heven) (baseFold d hd) i hi
  change (d : ℤ) + 1 - faceLiftPos (d * d - 2) (topLength_even d heven) (baseFold d hd) i 2 = d + 2
  rw [hh]
  omega

theorem topFold_P_outside_cube (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (hi : (faceWord (d * d - 2)).get i = .P) :
    (topFold d hd heven).pos i ∉ cube (fun _ => 0) (d + 2) := by
  intro hc
  have hy := (hc 1).2
  rw [topFold_P_height d hd heven i hi] at hy
  simp only [Nat.cast_add, Nat.cast_ofNat, zero_add] at hy
  omega

theorem topFold_last_adjacent_bridge (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    cubicLattice.Adj
      ((topFold d hd heven).pos
        (faceLastIndex (d * d - 2) (topLength_even d heven) (topLength_pos d hd)))
      (point d (d + 2) d) := by
  rw [topFold_last]
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [point]

theorem bridge_adjacent_bulk (d : ℕ) :
    cubicLattice.Adj (point d (d + 2) d) (point d (d + 1) d) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [point]

theorem topFold_first_of_val (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (hi : i.val = 0) :
    (topFold d hd heven).pos i = point (d - 1) (d + 2) 1 := by
  have he : i = faceFirstIndex _ (topLength_even d heven) (topLength_pos d hd) := Fin.ext hi
  rw [he]
  exact topFold_first d hd heven

theorem topFold_last_of_end (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (hi : i.val + 1 = (faceWord (d * d - 2)).length) :
    (topFold d hd heven).pos i = point (d - 1) (d + 2) d := by
  have he : i = faceLastIndex _ (topLength_even d heven) (topLength_pos d hd) := by
    apply Fin.ext
    change i.val = (faceWord (d * d - 2)).length - 1
    omega
  rw [he]
  exact topFold_last d hd heven

/-- The projection of every chain vertex, including every exterior P, lands
on one of the occupied H cells. In particular neither missing-hole column is
used by any residue in this component. -/
theorem topFold_column_support (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) :
    HSupport d (point ((topFold d hd heven).pos i 0) (d + 1) ((topFold d hd heven).pos i 2)) := by
  let k := faceBaseIndex (d * d - 2) (topLength_even d heven) i
  have hp : point ((topFold d hd heven).pos i 0) (d + 1) ((topFold d hd heven).pos i 2) =
      topMap d ((baseFold d hd).pos k) := by
    apply site_ext
    · rfl
    · change (d : ℤ) + 1 = (d : ℤ) + 1 - (baseFold d hd).pos k 2
      rw [baseFold_plane]
      omega
    · rfl
  rw [hp, ← topFold_hydrophobicSites]
  exact (topFold_hydrophobicSites_range d hd heven _).mpr ⟨k, rfl⟩

theorem topFold_avoids_hole_columns (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) :
    ¬ ((topFold d hd heven).pos i 0 = (d : ℤ) ∧
      ((topFold d hd heven).pos i 2 = (d : ℤ) ∨ (topFold d hd heven).pos i 2 = 1)) := by
  have hs := topFold_column_support d hd heven i
  rintro ⟨hx, hz | hz⟩
  · exact hs.2.2.2.1 (site_ext hx rfl hz)
  · exact hs.2.2.2.2 (site_ext hx rfl hz)

end ProteinFolding.CubicPackingTopFace
