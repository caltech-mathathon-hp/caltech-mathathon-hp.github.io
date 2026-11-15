import ProteinFolding.Tetrahedral.MainTheorem
import ProteinFolding.Tetrahedral.LocalStructure
import ProteinFolding.Tetrahedral.Layers
import ProteinFolding.Tetrahedral.FoldCounting
import ProteinFolding.Tetrahedral.LayerBounds
import ProteinFolding.Tetrahedral.RootSum
import ProteinFolding.Tetrahedral.LargePart
import ProteinFolding.Tetrahedral.BackwardBase

/-! Kernel-checked specification examples. These prove no complexity result. -/

namespace ProteinFolding.Tetrahedral.Examples

open Residue

-- Congruences select the intended two sublattices, including negative sites.
example : InASublattice ![0, 0, 0] := by decide
example : InBSublattice ![1, 1, 1] := by decide
example : InBSublattice ![-1, 1, -1] := by decide
example : InASublattice ![-2, 2, 0] := by decide
example : ¬ IsLatticeSite ![2, 0, 0] := by decide
example : ¬ IsLatticeSite ![1, 1, -1] := by decide
example : ¬ IsLatticeSite ![1, 0, 0] := by decide
example : ¬ IsLatticeSite ![1, 1, 0] := by decide

private def origin : Site := ⟨![0, 0, 0], by decide⟩
private def t1 : Site := ⟨![1, 1, 1], by decide⟩
private def t2 : Site := ⟨![1, -1, -1], by decide⟩
private def t3 : Site := ⟨![-1, 1, -1], by decide⟩
private def t4 : Site := ⟨![-1, -1, 1], by decide⟩
private def a022 : Site := ⟨![0, 2, 2], by decide⟩
private def a202 : Site := ⟨![2, 0, 2], by decide⟩
private def a220 : Site := ⟨![2, 2, 0], by decide⟩

-- All four A-to-B directions and all four reverse directions at a B-site.
example : tetrahedralLattice.Adj origin t1 := by decide
example : tetrahedralLattice.Adj origin t2 := by decide
example : tetrahedralLattice.Adj origin t3 := by decide
example : tetrahedralLattice.Adj origin t4 := by decide
example : tetrahedralLattice.Adj t1 origin := by decide
example : tetrahedralLattice.Adj t1 a022 := by decide
example : tetrahedralLattice.Adj t1 a202 := by decide
example : tetrahedralLattice.Adj t1 a220 := by decide
example : ¬ tetrahedralLattice.Adj origin a220 := by decide
example : ¬ tetrahedralLattice.Adj origin origin := by decide

-- The proved neighbour enumeration and finite-set counting use the same model.
example : neighbours origin = {t1, t2, t3, t4} := by decide
example : (neighbours origin).card = 4 := card_neighbours origin
example : neighboursAbove origin = {t1, t2} := by decide
example : neighboursBelow origin = {t3, t4} := by decide
example : (neighboursAbove t3).card = 2 := card_neighboursAbove t3
example : (neighboursBelow t3).card = 2 := card_neighboursBelow t3
example : internalEdgeCount {origin} = 0 := by decide
example : boundaryCount {origin} = 4 := by decide
example : internalEdgeCount {origin, t1} = 1 := by decide
example : boundaryCount {origin, t1} = 6 := by decide
example : internalEdgeCount (∅ : Finset Site) = 0 := by decide
example : boundaryCount (∅ : Finset Site) = 0 := by decide

-- Both gap parities, inverse steps, and a negative-coordinate site.
example : gapNext 0 origin = t1 := by decide
example : gapPrev 0 t1 = origin := by decide
example : gapPrev (-1) t3 = origin := by decide
example : gapChainKey 0 origin = gapChainKey 0 t1 := by decide
example : gapChainKey (-1) t3 = gapChainKey (-1) origin := by decide
example : gapPrev 0 (gapNext 0 origin) = origin := gapPrev_next _ _

-- Run counting agrees with actual gap boundary bonds.
example : gapRunCount {origin} (-1) = 1 := by decide
example : gapRunCount {origin} 0 = 1 := by decide
example : gapRunCount {origin} 1 = 0 := by decide
example : gapRunCount {origin, t1} 0 = 1 := by decide
example : gapBoundaryCount {origin, t1} 0 = 2 := by decide
example : totalRuns {origin, t1} = 3 := by decide
example : runsBefore {origin} 0 = 1 := by decide
example : runsFrom {origin} 0 = 1 := by decide
example : (finiteLayer {origin, t1} 0).card = 1 := by decide
example : boundaryCount {origin, t1} = 2 * totalRuns {origin, t1} :=
  boundaryCount_eq_twice_totalRuns _

-- The integer square-root sum and the octahedral number sequence.
private theorem rootSumFour : rootSum 4 = 3 := by
  have h := rootSum_square_polynomial 2
  change 6 * rootSum 4 + 3 * 4 + 2 = 4 * 8 at h
  omega

private theorem rootSumNine : rootSum 9 = 13 := by
  have h := rootSum_square_polynomial 3
  change 6 * rootSum 9 + 3 * 9 + 3 = 4 * 27 at h
  omega

private theorem sqrtEight : Nat.sqrt 8 = 2 := Nat.sqrt_add_eq' 2 (a := 4) (by decide)

example : rootSum 9 = 13 := rootSumNine
example : rootWindow 4 9 = 10 := by rw [rootWindow, rootSumFour, rootSumNine]
example : octahedralNumber 1 = 1 := by rw [octahedralNumber_formula]; decide
example : octahedralNumber 2 = 10 := by rw [octahedralNumber_formula]; decide
example : octahedralNumber 3 = 35 := by rw [octahedralNumber_formula]; decide
example : octahedralNumber 4 = 84 := by rw [octahedralNumber_formula]; decide

private def canonicalThree : PositiveComposition :=
  .snoc (.snoc (.snoc (.snoc (.single 1 (by decide)) 1 (by decide))
    2 (by decide)) 2 (by decide)) 3 (by decide)

example : canonicalThree.parts = [1, 1, 2, 2, 3] := by rfl
example : canonicalThree.mass = 9 := by decide
example : canonicalThree.value = rootSum canonicalThree.mass := by
  change 13 = rootSum 9
  rw [rootSumNine]
example : nextSquareDistance 8 = 1 := by rw [nextSquareDistance, sqrtEight]; decide
example : Nat.sqrt 8 * 4 + (4 - nextSquareDistance 8) = rootWindow 8 12 := by
  have h8 : rootSum 8 = rootSum 4 + 2 * 4 := rootSum_square_block 2 4 (by decide)
  have h12 : rootSum 12 = rootSum 9 + 3 * 3 := rootSum_square_block 3 3 (by decide)
  rw [rootWindow, nextSquareDistance, sqrtEight, h8, h12, rootSumFour, rootSumNine]
  decide
example : largePartPenalty 2 1 2 2 = 3 := by decide
example : rootWindow 2 5 + 1 = 5 := rootWindow_base_low 2 1 (by decide) (by decide) (by decide)
example : rootWindow 4 7 = 6 := rootWindow_base_high 2 3 (by decide) (by decide)

private def twoHFold : Fold tetrahedralLattice [H, H].length where
  pos i := if i.val = 0 then origin else t1
  injective_pos := by decide
  consecutive := by decide

-- In this manuscript the backbone H-H bond does contribute to the score.
example : bondCount [H, H] twoHFold = 1 := by decide
example : HPStringFold [H, H] 1 := ⟨twoHFold, by decide⟩
example : bondCount [H, P] twoHFold = 0 := by decide

private def hexagon : Fin 6 → Site :=
  ![origin, t1, a022, ⟨![-1, 3, 1], by decide⟩,
    ⟨![-2, 2, 0], by decide⟩, t3]

private def hexagonFold : Fold tetrahedralLattice [H, H, H, H, H, H].length where
  pos := hexagon
  injective_pos := by decide
  consecutive := by decide

-- Five backbone bonds and one endpoint contact, counted once each.
example : bondCount [H, H, H, H, H, H] hexagonFold = 6 := by decide
example : bondCount [H, P, P, P, P, H] hexagonFold = 1 := by decide
example : HPStringFold [H, H, H, H, H, H] 6 := ⟨hexagonFold, by decide⟩

-- The geometric count includes all six edges, not just the five chain bonds.
example : internalEdgeCount (hSupport [H, H, H, H, H, H] hexagonFold) = 6 := by
  rw [← bondCount_eq_internalEdgeCount]
  decide

example : boundaryCount (hSupport [H, H, H, H, H, H] hexagonFold) = 12 := by
  have h := fold_boundary_identity [H, H, H, H, H, H] hexagonFold
  have hc : hydrophobicCount [H, H, H, H, H, H] = 6 := by decide
  have hb : bondCount [H, H, H, H, H, H] hexagonFold = 6 := by decide
  rw [hc, hb] at h
  omega

private def emptyFold : Fold tetrahedralLattice ([] : Sequence).length where
  pos := Fin.elim0
  injective_pos := by decide
  consecutive := by decide

example : bondCount [] emptyFold = 0 := by decide
example : HPStringFold [] 0 := ⟨emptyFold, by decide⟩
example : HPStringFold [] (-1) := ⟨emptyFold, by decide⟩
example (I : HPInstance) : hpEncoding.decode (hpEncoding.encode I) = some I :=
  hpEncoding.decode_encode I

-- Expanding the target gives precisely the existing universal NP definition.
example : HPStringFoldNPComplete ↔
    InNP hpEncoding (fun I : HPInstance => I.Accepts) ∧
    NPHard hpEncoding (fun I : HPInstance => I.Accepts) := Iff.rfl

end ProteinFolding.Tetrahedral.Examples
