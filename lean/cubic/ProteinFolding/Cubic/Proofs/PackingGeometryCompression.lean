import ProteinFolding.Cubic.Proofs.PackingGeometryLocal
import ProteinFolding.Cubic.Proofs.VerifierRecords

/-! Compression of H-P-P-H bridges in a perfect cube fold. This proves
Fact 3.11 of Berger--Leighton, Section 3.2.4, without fixing a face in advance. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

def oppositeDirection : Fin 6 → Fin 6
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4

theorem step_commute (p : Site) (d e : Fin 6) :
    step (step p d) e = step (step p e) d := by
  funext k
  simp only [CubicVerifier.step_increment]
  omega

theorem step_reverse (p : Site) (d : Fin 6) :
    step (step p d) (oppositeDirection d) = p := by
  funext k
  simp only [CubicVerifier.step_increment]
  fin_cases d <;> fin_cases k <;> simp [TM2WalkCounters.increment, oppositeDirection]

set_option maxHeartbeats 1000000 in
/-- After a step leaving a cube, returning in two further steps must use
the reverse direction. This proof only examines the violated coordinate. -/
theorem return_uses_reverse (a p : Site) (n : ℕ) (d e g : Fin 6)
    (hp : p ∈ cube a n) (hu : step p d ∉ cube a n)
    (hq : step (step (step p d) e) g ∈ cube a n) :
    e = oppositeDirection d ∨ g = oppositeDirection d := by
  by_contra h
  have he : e ≠ oppositeDirection d := fun he => h (Or.inl he)
  have hg : g ≠ oppositeDirection d := fun hg => h (Or.inr hg)
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hq0 := hq 0
  have hq1 := hq 1
  have hq2 := hq 2
  simp only [CubicVerifier.step_increment] at hq0 hq1 hq2
  rw [cube_mem_coordinates] at hu
  fin_cases d
  all_goals simp only [oppositeDirection] at he hg
  all_goals simp only [step, Fin.reduceFinMk, ↓reduceIte] at hu
  all_goals simp only [TM2WalkCounters.increment, Fin.reduceFinMk, ↓reduceIte] at hq0 hq1 hq2
  all_goals split_ifs at hq0 <;> omega

/-- Three unit steps with both intermediate sites outside a cube and both
endpoints inside it must have adjacent endpoints. -/
theorem exterior_three_step_compress (a p u v q : Site) (n : ℕ)
    (hp : p ∈ cube a n) (hq : q ∈ cube a n)
    (hu : u ∉ cube a n) (hv : v ∉ cube a n)
    (hpu : cubicLattice.Adj p u) (huv : cubicLattice.Adj u v)
    (hvq : cubicLattice.Adj v q) : cubicLattice.Adj p q := by
  obtain ⟨d, rfl⟩ := adj_step hpu
  obtain ⟨e, rfl⟩ := adj_step huv
  obtain ⟨g, rfl⟩ := adj_step hvq
  rcases return_uses_reverse a p n d e g hp hu hq with he | hg
  · subst e
    rw [step_reverse] at hv
    exact False.elim (hv hp)
  · subst g
    rw [step_commute (step p d) e (oppositeDirection d), step_reverse]
    exact step_adj p e

/-- Fact 3.11 for consecutive indices in an arbitrary larger sequence. -/
theorem hpph_adjacent {S : Sequence} (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hpack : hydrophobicSites S f = cube a n)
    (i j k l : Fin S.length)
    (hij : i.val + 1 = j.val) (hjk : j.val + 1 = k.val) (hkl : k.val + 1 = l.val)
    (hi : S.get i = .H) (hj : S.get j = .P)
    (hk : S.get k = .P) (hl : S.get l = .H) : cubicLattice.Adj (f.pos i) (f.pos l) :=
  exterior_three_step_compress a (f.pos i) (f.pos j) (f.pos k) (f.pos l) n
    (h_mem_cube f a n hpack i hi) (h_mem_cube f a n hpack l hl)
    (p_not_mem_cube f a n hpack j hj) (p_not_mem_cube f a n hpack k hk)
    (f.consecutive i j hij) (f.consecutive j k hjk) (f.consecutive k l hkl)

end ProteinFolding.CubicPackingGeometry
