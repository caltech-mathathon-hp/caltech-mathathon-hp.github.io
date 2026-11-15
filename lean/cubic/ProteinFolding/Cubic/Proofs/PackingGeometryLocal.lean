import ProteinFolding.Cubic.Proofs.CertificatesDirections
import Mathlib.Tactic.FinCases

/-! Local forcing facts for the packing reduction (Berger--Leighton,
Section 3.2.4, Facts 3.9--3.11). Exact H occupation excludes every P from
the cube; two exterior backbone neighbours force an H onto its edge skeleton.
An exterior H-P-P-H bridge compresses to one lattice edge. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

/-- A coordinate lies on one of the two supporting faces of a lattice cube. -/
def BoundaryCoordinate (a p : Site) (n : ℕ) (k : Fin 3) : Prop :=
  p k = a k ∨ p k + 1 = a k + (n : ℤ)

/-- The union of cube edges, including its corners. -/
def EdgeSkeleton (a : Site) (n : ℕ) (p : Site) : Prop :=
  p ∈ cube a n ∧ ∃ i j : Fin 3, i ≠ j ∧
    BoundaryCoordinate a p n i ∧ BoundaryCoordinate a p n j

def Surface (a : Site) (n : ℕ) (p : Site) : Prop :=
  p ∈ cube a n ∧ ∃ k : Fin 3, BoundaryCoordinate a p n k

/-- Any P position is outside the cube whenever the H support fills it exactly. -/
theorem p_not_mem_cube {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites S f = cube a n)
    (i : Fin S.length) (hi : S.get i = .P) : f.pos i ∉ cube a n := by
  intro hmem
  rw [← hpack] at hmem
  obtain ⟨j, hj, hji⟩ := hmem
  have he : j = i := f.injective_pos hji
  subst j
  rw [hi] at hj
  contradiction

theorem h_mem_cube {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites S f = cube a n)
    (i : Fin S.length) (hi : S.get i = .H) : f.pos i ∈ cube a n := by
  rw [← hpack]
  exact ⟨i, hi, rfl⟩

theorem cube_mem_coordinates (a p : Site) (n : ℕ) :
    p ∈ cube a n ↔
      (a 0 ≤ p 0 ∧ p 0 < a 0 + (n : ℤ)) ∧
      (a 1 ≤ p 1 ∧ p 1 < a 1 + (n : ℤ)) ∧
      (a 2 ≤ p 2 ∧ p 2 < a 2 + (n : ℤ)) := by
  constructor
  · intro hp
    exact ⟨hp 0, hp 1, hp 2⟩
  · rintro ⟨h0, h1, h2⟩ k
    fin_cases k <;> assumption

theorem surface_of_exterior_neighbour (a p u : Site) (n : ℕ)
    (hp : p ∈ cube a n) (hpu : cubicLattice.Adj p u) (hu : u ∉ cube a n) :
    Surface a n p := by
  obtain ⟨d, rfl⟩ := adj_step hpu
  refine ⟨hp, ?_⟩
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  rw [cube_mem_coordinates] at hu
  fin_cases d
  all_goals simp only [step, Fin.reduceFinMk, ↓reduceIte] at hu
  all_goals first
    | refine ⟨0, ?_⟩; simp only [BoundaryCoordinate]; omega
    | refine ⟨1, ?_⟩; simp only [BoundaryCoordinate]; omega
    | refine ⟨2, ?_⟩; simp only [BoundaryCoordinate]; omega

/-- Two distinct exterior neighbours force two boundary-coordinate axes.
The degenerate side-one case is included: its single site lies on every face. -/
theorem edgeSkeleton_of_two_exterior_neighbours (a p u v : Site) (n : ℕ)
    (hp : p ∈ cube a n) (hpu : cubicLattice.Adj p u) (hpv : cubicLattice.Adj p v)
    (hu : u ∉ cube a n) (hv : v ∉ cube a n) (huv : u ≠ v) :
    EdgeSkeleton a n p := by
  obtain ⟨d, rfl⟩ := adj_step hpu
  obtain ⟨e, rfl⟩ := adj_step hpv
  refine ⟨hp, ?_⟩
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  rw [cube_mem_coordinates] at hu hv
  fin_cases d <;> fin_cases e
  all_goals simp only [step, Fin.reduceFinMk, ↓reduceIte] at hu hv huv
  all_goals first
    | exact False.elim (huv rfl)
    | refine ⟨0, 1, by decide, ?_, ?_⟩ <;> simp only [BoundaryCoordinate] <;> omega
    | refine ⟨0, 2, by decide, ?_, ?_⟩ <;> simp only [BoundaryCoordinate] <;> omega
    | refine ⟨1, 2, by decide, ?_, ?_⟩ <;> simp only [BoundaryCoordinate] <;> omega

/-- Fact 3.9, expressed directly for a P-H-P occurrence in an arbitrary
perfect fold. The neighbouring sequence indices may belong to any larger word. -/
theorem php_on_edge {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites S f = cube a n)
    (i j k : Fin S.length) (hij : i.val + 1 = j.val) (hjk : j.val + 1 = k.val)
    (hi : S.get i = .P) (hj : S.get j = .H) (hk : S.get k = .P) :
    EdgeSkeleton a n (f.pos j) := by
  apply edgeSkeleton_of_two_exterior_neighbours a (f.pos j) (f.pos i) (f.pos k) n
  · exact h_mem_cube f a n hpack j hj
  · exact (f.consecutive i j hij).symm
  · exact f.consecutive j k hjk
  · exact p_not_mem_cube f a n hpack i hi
  · exact p_not_mem_cube f a n hpack k hk
  · intro he
    have h := congrArg Fin.val (f.injective_pos he)
    omega

/-- Fact 3.10: an H adjoining a P lies on the cube's surface. -/
theorem hp_on_surface {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites S f = cube a n)
    (i j : Fin S.length) (hij : cubicLattice.Adj (f.pos i) (f.pos j))
    (hi : S.get i = .H) (hj : S.get j = .P) : Surface a n (f.pos i) :=
  surface_of_exterior_neighbour a (f.pos i) (f.pos j) n
    (h_mem_cube f a n hpack i hi) hij (p_not_mem_cube f a n hpack j hj)

end ProteinFolding.CubicPackingGeometry
