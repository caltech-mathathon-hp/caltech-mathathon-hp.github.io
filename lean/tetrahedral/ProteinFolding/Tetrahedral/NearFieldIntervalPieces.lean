import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.NearFieldWordTransport
import ProteinFolding.Tetrahedral.NearFieldDimerBounds
import ProteinFolding.Tetrahedral.NearFieldDimerBulkClearance

/-! Actual positive dimer words on any reserved edge interval, including their
two caps, support, endpoints and locality. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem positive_dimer_word (n : ℕ) (hn : 0 < n) : dimerChain (n - 1 + 1) = dimerChain n := by
  congr 1
  omega

def intervalDimerFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1) :
    Fold tetrahedralLattice (dimerChain n).length :=
  transportWordFold (positive_dimer_word n hn)
    (edgeDimerFold hm F base (n - 1) reverse (by omega))

theorem intervalDimerFold_hSupport {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1) :
    hSupport (dimerChain n) (intervalDimerFold hm F base n hn reverse hroom) =
      edgeDimerHsites m F base (n - 1) := by
  rw [intervalDimerFold, transportWordFold_hSupport, edgeDimerFold_hSupport]

def cappedIntervalDimerFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1)) :
    Fold tetrahedralLattice (capWord (dimerChain n)).length :=
  transportWordFold (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) C D hC hD)

theorem cappedIntervalDimerFold_hSupport {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1)) :
    hSupport (capWord (dimerChain n)) (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD) =
      edgeDimerHsites m F base (n - 1) := by
  rw [cappedIntervalDimerFold, transportWordFold_hSupport, cappedEdgeDimerFold_hSupport]

theorem cappedIntervalDimerFold_sites {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1)) :
    foldSites (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD) =
      foldSites (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) C D hC hD) := by
  rw [cappedIntervalDimerFold, transportWordFold_sites]

theorem cappedIntervalDimerFold_first {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) (hi : i.val = 0) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i = C.seed := by
  apply transportWordFold_first
  · exact cappedWordFold_first _ _ _ _ _ _ _ _ _
  · exact hi

theorem cappedIntervalDimerFold_last {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) (hi : i.val + 1 = (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i = D.seed := by
  apply transportWordFold_last
  · exact cappedWordFold_last _ _ _ _ _ _ _ _ _
  · exact hi

def cappedIntervalDimerPiece {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1)) : PositionedWord where
  word := capWord (dimerChain n)
  fold := cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD
  length_pos := by
    change 0 < (capWord (dimerChain n)).length
    exact Nat.succ_pos _
  first := C.seed
  last := D.seed
  first_eq := cappedIntervalDimerFold_first hm F base n hn reverse hroom C D hC hD
  last_eq := cappedIntervalDimerFold_last hm F base n hn reverse hroom C D hC hD

theorem cappedIntervalDimerFold_mem_solid_one {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base n : ℕ)
    (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * m - 1)
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i ∈ skinSolid m 1 := by
  exact transportWordFold_property _ _ _ (cappedEdgeDimerFold_mem_solid_one hm F base (n - 1)
    reverse (by omega) C D hC hD) i

theorem cappedIntervalDimerFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (E : DanglingColumn m) (hE : E.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m E.owner).card = 1)
    (i : Fin (capWord (dimerChain n)).length) (r : ℕ) :
    (cappedIntervalDimerFold (m := m) (by omega) F base n hn reverse hroom C D hC hD).pos i ≠ E.point r := by
  have hm1 : 1 ≤ m := by omega
  have hroom' : base + 2 * (n - 1 + 1) ≤ 2 * m - 1 := by omega
  exact transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm1 F base (n - 1) reverse hroom' C D hC hD)
    (fun x : Site => x ≠ E.point r)
    (fun j => cappedEdgeDimerFold_ne_bulkEndColumn m hm F base (n - 1) reverse hroom'
      C D hC hD E hE hend j r) i

end ProteinFolding.Tetrahedral.NearField
