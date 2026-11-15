import ProteinFolding.Cubic.Statement
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite geometric interfaces for the cubic HP model

These lemmas connect the frozen set-valued packing condition to finite sets.
They do not use an isoperimetric inequality.
-/

namespace ProteinFolding.CubicGeometry

open scoped BigOperators

def hSupport (S : Sequence) (f : Fold cubicLattice S.length) : Finset Site :=
  (hydrophobicIndices S).image f.pos

theorem mem_hSupport (S : Sequence) (f : Fold cubicLattice S.length) (p : Site) :
    p ∈ hSupport S f ↔ p ∈ hydrophobicSites S f := by
  simp [hSupport, hydrophobicSites, hydrophobicIndices]

theorem hSupport_card (S : Sequence) (f : Fold cubicLattice S.length) :
    (hSupport S f).card = hydrophobicCount S := by
  exact Finset.card_image_of_injective _ f.injective_pos

def cubePoint (a : Site) {n : ℕ} (q : Fin 3 → Fin n) : Site :=
  fun k => a k + (q k).val

theorem cubePoint_injective (a : Site) (n : ℕ) :
    Function.Injective (cubePoint a : (Fin 3 → Fin n) → Site) := by
  intro q r h
  funext k
  apply Fin.ext
  have hk := congrFun h k
  change a k + ((q k).val : ℤ) = a k + ((r k).val : ℤ) at hk
  omega

def cubeFinset (a : Site) (n : ℕ) : Finset Site :=
  Finset.univ.image (cubePoint a : (Fin 3 → Fin n) → Site)

theorem mem_cubeFinset (a : Site) (n : ℕ) (p : Site) :
    p ∈ cubeFinset a n ↔ p ∈ cube a n := by
  classical
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    intro k
    change a k ≤ a k + ((q k).val : ℤ) ∧
      a k + ((q k).val : ℤ) < a k + (n : ℤ)
    have hk := (q k).isLt
    omega
  · intro hp
    let q : Fin 3 → Fin n := fun k =>
      ⟨(p k - a k).toNat, by
        have hk := hp k
        exact (Int.toNat_lt (by omega)).mpr (by omega)⟩
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    funext k
    have hk := hp k
    have hn : 0 ≤ p k - a k := by omega
    change a k + ((p k - a k).toNat : ℤ) = p k
    rw [Int.toNat_of_nonneg hn]
    omega

theorem cubeFinset_card (a : Site) (n : ℕ) : (cubeFinset a n).card = n ^ 3 := by
  classical
  rw [cubeFinset, Finset.card_image_of_injective _ (cubePoint_injective a n)]
  simp

theorem cube_zero (a : Site) : cube a 0 = ∅ := by
  ext p
  constructor
  · intro hp
    have h := hp (0 : Fin 3)
    simp only [Nat.cast_zero, add_zero] at h
    omega
  · simp

theorem cube_one (a : Site) : cube a 1 = {a} := by
  ext p
  constructor
  · intro hp
    have he : p = a := by
      funext k
      have h := hp k
      simp only [Nat.cast_one] at h
      omega
    exact he
  · intro hp
    have he : p = a := hp
    subst p
    intro k
    simp

theorem packsCube_iff_finset (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ) :
    PacksCube S f n ↔ ∃ a, hSupport S f = cubeFinset a n := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext p
    rw [mem_hSupport, mem_cubeFinset, ha]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext p
    rw [← mem_hSupport, ← mem_cubeFinset, ha]

theorem packsCube_count (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ)
    (h : PacksCube S f n) : hydrophobicCount S = n ^ 3 := by
  obtain ⟨a, ha⟩ := (packsCube_iff_finset S f n).mp h
  rw [← hSupport_card S f, ha, cubeFinset_card]

theorem packsCube_zero_of_count_zero (S : Sequence) (f : Fold cubicLattice S.length)
    (h : hydrophobicCount S = 0) : PacksCube S f 0 := by
  have he : hSupport S f = ∅ := Finset.card_eq_zero.mp ((hSupport_card S f).trans h)
  refine ⟨fun _ => 0, ?_⟩
  rw [cube_zero]
  ext p
  rw [← mem_hSupport, he]
  simp

theorem packsCube_one_of_count_one (S : Sequence) (f : Fold cubicLattice S.length)
    (h : hydrophobicCount S = 1) : PacksCube S f 1 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp ((hSupport_card S f).trans h)
  refine ⟨a, ?_⟩
  rw [cube_one]
  ext p
  rw [← mem_hSupport, ha]
  simp

theorem perfectIffThreshold_side_zero (I : PerfectInstance) (h : I.side = 0) :
    I.Accepts ↔ HPStringFold (G := cubicLattice) I.sequence (cubeBondThreshold I.side) := by
  have hc : hydrophobicCount I.sequence = 0 := by simpa [h] using I.count_eq
  constructor
  · rintro ⟨f, _⟩
    refine ⟨f, ?_⟩
    simp [h, cubeBondThreshold]
  · rintro ⟨f, _⟩
    exact ⟨f, h ▸ packsCube_zero_of_count_zero I.sequence f hc⟩

theorem perfectIffThreshold_side_one (I : PerfectInstance) (h : I.side = 1) :
    I.Accepts ↔ HPStringFold (G := cubicLattice) I.sequence (cubeBondThreshold I.side) := by
  have hc : hydrophobicCount I.sequence = 1 := by simpa [h] using I.count_eq
  constructor
  · rintro ⟨f, _⟩
    refine ⟨f, ?_⟩
    simp [h, cubeBondThreshold]
  · rintro ⟨f, _⟩
    exact ⟨f, h ▸ packsCube_one_of_count_one I.sequence f hc⟩

end ProteinFolding.CubicGeometry
