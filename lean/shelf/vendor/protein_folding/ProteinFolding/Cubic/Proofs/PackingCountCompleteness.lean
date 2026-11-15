import ProteinFolding.Cubic.Proofs.GeometryBasics
import ProteinFolding.Cubic.Proofs.PackingWords

/-! Equal finite volume turns hydrophobic containment into exact occupation.
Completeness constructions need only put all H residues inside the cube; the
proved word count and self-avoidance then fill every cube site automatically. -/

namespace ProteinFolding.CubicGeometry

theorem hydrophobicSites_eq_cube_of_inside_of_count (S : Sequence)
    (f : Fold cubicLattice S.length) (a : Site) (n : ℕ)
    (hcount : hydrophobicCount S = n ^ 3)
    (hinside : hydrophobicSites S f ⊆ cube a n) : hydrophobicSites S f = cube a n := by
  have hsub : hSupport S f ⊆ cubeFinset a n := by
    intro p hp
    exact (mem_cubeFinset a n p).mpr (hinside ((mem_hSupport S f p).mp hp))
  have he : hSupport S f = cubeFinset a n := Finset.eq_of_subset_of_card_le hsub (by
    rw [cubeFinset_card, hSupport_card, hcount])
  ext p
  rw [← mem_hSupport, he, mem_cubeFinset]

theorem packsCube_of_inside_of_count (S : Sequence) (f : Fold cubicLattice S.length)
    (a : Site) (n : ℕ) (hcount : hydrophobicCount S = n ^ 3)
    (hinside : hydrophobicSites S f ⊆ cube a n) : PacksCube S f n :=
  ⟨a, hydrophobicSites_eq_cube_of_inside_of_count S f a n hcount hinside⟩

end ProteinFolding.CubicGeometry

namespace ProteinFolding.CubicPacking

theorem frameWord_perfect_of_inside (q Q : ℕ) (items : List ℕ) (hq : 0 < q)
    (hsum : items.sum = q * (4 * Q)) (f : Fold cubicLattice (frameWord q Q items).length)
    (hinside : hydrophobicSites (frameWord q Q items) f ⊆ cube (fun _ => 0) (side q Q)) :
    PerfectHPStringFold (frameWord q Q items) (side q Q) :=
  ⟨frameWord_count q Q items hq hsum, f,
    CubicGeometry.packsCube_of_inside_of_count _ f _ _ (frameWord_count q Q items hq hsum) hinside⟩

end ProteinFolding.CubicPacking
