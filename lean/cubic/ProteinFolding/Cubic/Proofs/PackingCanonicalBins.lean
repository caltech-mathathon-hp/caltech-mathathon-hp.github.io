import ProteinFolding.Cubic.Proofs.PackingGeometryLargeFaces
import ProteinFolding.Cubic.Proofs.PackingGeometryAnchorIntervals

/-! The complementary strips between canonical wall levels. Every interior
coordinate avoiding all wall rows belongs to one bin, and a connected path
avoiding the two bounding rows stays in that bin. -/

namespace ProteinFolding.CubicPackingGeometry

theorem exists_canonical_bin (q width k : ℕ) (hq : 0 < q) (hw : 2 < width)
    (hk : 1 ≤ k ∧ k ≤ q * width)
    (hleft : ∀ j : Fin q, k ≠ j.val * width + 1)
    (hright : ∀ j : Fin q, k ≠ (j.val + 1) * width) :
    ∃ j : Fin q, j.val * width + 1 < k ∧ k < (j.val + 1) * width := by
  have hlast := hright (⟨q - 1, by omega⟩ : Fin q)
  have hqeq : q - 1 + 1 = q := by omega
  simp only [hqeq] at hlast
  have hklt : k < q * width := by omega
  have hjlt : k / width < q := (Nat.div_lt_iff_lt_mul (by omega)).mpr hklt
  let j : Fin q := ⟨k / width, hjlt⟩
  have hmod := Nat.mod_lt k (by omega : 0 < width)
  have he := Nat.div_add_mod k width
  rw [Nat.mul_comm width (k / width)] at he
  have hr0 : k % width ≠ 0 := by
    intro hr
    by_cases hj : k / width = 0
    · simp only [hj, hr, Nat.zero_mul, Nat.zero_add] at he
      omega
    · let prev : Fin q := ⟨k / width - 1, (Nat.sub_le _ _).trans_lt hjlt⟩
      have hp : prev.val + 1 = k / width := Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)
      have hb := hright prev
      rw [hp] at hb
      apply hb
      rw [hr, Nat.add_zero] at he
      exact he.symm
  have hr1 : k % width ≠ 1 := by
    intro hr
    have hb := hleft j
    dsimp [j] at hb
    apply hb
    rw [hr] at he
    exact he.symm
  refine ⟨j, ?_⟩
  dsimp [j]
  constructor
  · omega
  · rw [Nat.add_mul, Nat.one_mul]
    omega

theorem railCoordinate_of_face {a p : Site} {d : ℕ} {face : CubeFace} {axis : Fin 3}
    (hface : FaceInterior a (d + 2) face.1 face.2 p) (haxis : axis ≠ face.1) :
    1 ≤ railCoordinate a axis p ∧ railCoordinate a axis p ≤ d ∧
      p axis = a axis + (railCoordinate a axis p : ℤ) := by
  have hp := hface.2.2 axis haxis
  unfold railCoordinate
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ p axis - a axis)]
  omega

/-- A connected face path avoiding every canonical wall row occupies one
of the q complementary strips. The path need not be straight or rectangular. -/
theorem exists_bin_for_face_path (q width d : ℕ) (hq : 0 < q) (hw : 2 < width)
    (hd : d = q * width) (a : Site) (face : CubeFace) (axis : Fin 3)
    (haxis : axis ≠ face.1) {N : ℕ} (p : Fin N → Site) (hN : 0 < N)
    (hface : ∀ i, FaceInterior a (d + 2) face.1 face.2 (p i))
    (hstep : ∀ i j : Fin N, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j))
    (havoid : ∀ (i : Fin N) (j : Fin q),
      railCoordinate a axis (p i) ≠ j.val * width + 1 ∧
        railCoordinate a axis (p i) ≠ (j.val + 1) * width) :
    ∃ j : Fin q, ∀ i,
      a axis + ((j.val * width + 1 : ℕ) : ℤ) < p i axis ∧
        p i axis < a axis + (((j.val + 1) * width : ℕ) : ℤ) := by
  let first : Fin N := ⟨0, hN⟩
  have hfirst := railCoordinate_of_face (hface first) haxis
  obtain ⟨j, hlo, hhi⟩ := exists_canonical_bin q width (railCoordinate a axis (p first)) hq hw
    (by simpa only [hd] using And.intro hfirst.1 hfirst.2.1)
    (fun j => (havoid first j).1) (fun j => (havoid first j).2)
  refine ⟨j, ?_⟩
  apply coordinate_strip_path_closed p hN
    (a axis + ((j.val * width + 1 : ℕ) : ℤ))
    (a axis + (((j.val + 1) * width : ℕ) : ℤ)) axis
  · change a axis + ((j.val * width + 1 : ℕ) : ℤ) < p first axis ∧
      p first axis < a axis + (((j.val + 1) * width : ℕ) : ℤ)
    omega
  · intro i
    have hc := (railCoordinate_of_face (hface i) haxis).2.2
    have ha := havoid i j
    constructor <;> intro he <;> apply ha.1 <;> omega
  · exact hstep

def canonicalBinRegion (a : Site) (d width : ℕ) (face : CubeFace)
    (x axis : Fin 3) {q : ℕ} (j : Fin q) : Finset Site :=
  faceStripFinset a d face.1 face.2 x axis
    (a axis + ((j.val * width + 1 : ℕ) : ℤ))
    (a axis + (((j.val + 1) * width : ℕ) : ℤ))

theorem canonicalBinRegion_card (a : Site) (d width : ℕ) (face : CubeFace)
    (x axis : Fin 3) (hxa : x ≠ axis) {q : ℕ} (j : Fin q) :
    (canonicalBinRegion a d width face x axis j).card = d * (width - 2) := by
  rw [canonicalBinRegion, faceStripFinset_card a d face.1 face.2 x axis hxa]
  have he : a axis + (((j.val + 1) * width : ℕ) : ℤ) -
      (a axis + ((j.val * width + 1 : ℕ) : ℤ)) - 1 = (width : ℤ) - 2 := by
    push_cast
    ring
  rw [he]
  congr 1
  omega

end ProteinFolding.CubicPackingGeometry
