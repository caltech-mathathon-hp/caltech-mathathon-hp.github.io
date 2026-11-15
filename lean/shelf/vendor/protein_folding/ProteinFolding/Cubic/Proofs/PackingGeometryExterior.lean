import ProteinFolding.Cubic.Proofs.PackingGeometryCompression

/-! An exterior lattice site has at most one neighbour inside a rectangular
cube. Consequently exterior P sites attached to different H sites are distinct. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

theorem return_in_one_uses_reverse (a p : Site) (n : ℕ) (d e : Fin 6)
    (hp : p ∈ cube a n) (hu : step p d ∉ cube a n)
    (hq : step (step p d) e ∈ cube a n) : e = oppositeDirection d := by
  by_contra he
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hq0 := hq 0
  have hq1 := hq 1
  have hq2 := hq 2
  simp only [CubicVerifier.step_increment] at hq0 hq1 hq2
  rw [cube_mem_coordinates] at hu
  fin_cases d
  all_goals simp only [oppositeDirection] at he
  all_goals simp only [step, Fin.reduceFinMk, ↓reduceIte] at hu
  all_goals simp only [TM2WalkCounters.increment, Fin.reduceFinMk, ↓reduceIte] at hq0 hq1 hq2
  all_goals split_ifs at hq0 <;> omega

/-- Every exterior site has a unique cube neighbour, whenever one exists. -/
theorem cube_exterior_neighbour_unique (a : Site) (n : ℕ) (u p q : Site)
    (hu : u ∉ cube a n) (hp : p ∈ cube a n) (hq : q ∈ cube a n)
    (hup : cubicLattice.Adj u p) (huq : cubicLattice.Adj u q) : p = q := by
  obtain ⟨d, rfl⟩ := adj_step hup.symm
  obtain ⟨e, rfl⟩ := adj_step huq
  have he := return_in_one_uses_reverse a p n d e hp hu hq
  subst e
  exact (step_reverse p d).symm

theorem exterior_attachments_distinct (a : Site) (n : ℕ) (u v p q : Site)
    (hu : u ∉ cube a n) (hv : v ∉ cube a n) (hp : p ∈ cube a n) (hq : q ∈ cube a n)
    (hup : cubicLattice.Adj u p) (hvq : cubicLattice.Adj v q) (hpq : p ≠ q) : u ≠ v := by
  intro he
  subst v
  exact hpq (cube_exterior_neighbour_unique a n u p q hu hp hq hup hvq)

end ProteinFolding.CubicPackingGeometry
