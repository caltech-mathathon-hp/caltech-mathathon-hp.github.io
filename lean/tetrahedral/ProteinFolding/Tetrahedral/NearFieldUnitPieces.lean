import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.NearFieldSeparatorCapSupport
import ProteinFolding.Tetrahedral.NearFieldLeftFillerCaps
import ProteinFolding.Tetrahedral.NearFieldTerminalColumn

/-! The actual capped separator, special filler, singleton and terminal units
in the common finite-word assembly interface. -/

namespace ProteinFolding.Tetrahedral.NearField

def separatorWordPiece (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) : PositionedWord where
  word := capWord (p.separatorWord k)
  fold := cappedSeparatorFold p k hk C D hC hD
  length_pos := by
    change 0 < (capWord (p.separatorWord k)).length
    exact Nat.succ_pos _
  first := C.seed
  last := D.seed
  first_eq := cappedSeparatorFold_first p k hk C D hC hD
  last_eq := cappedSeparatorFold_last p k hk C D hC hD

def leftFillerWordPiece (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) : PositionedWord where
  word := capWord (dimerChain p.leftFiller)
  fold := cappedLeftFillerFold p C D hC hD
  length_pos := by
    change 0 < (capWord (dimerChain p.leftFiller)).length
    exact Nat.succ_pos _
  first := C.seed
  last := D.seed
  first_eq := cappedWordFold_first _ _ _ _ _ _ _ _ _
  last_eq := cappedWordFold_last _ _ _ _ _ _ _ _ _

def oneHFold (p : Site) : Fold tetrahedralLattice ([Residue.H] : Sequence).length where
  pos _ := p
  injective_pos i j _ := by
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega
  consecutive i j hij := by
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega

theorem hSupport_oneHFold (p : Site) : hSupport [Residue.H] (oneHFold p) = {p} := by
  change hSupport (List.replicate 1 Residue.H) (oneHFold p) = {p}
  rw [hSupport_allH_eq_foldSites]
  ext x
  simp [foldSites, oneHFold]

theorem columnOwner_ne_seed {m : ℕ} (C : DanglingColumn m) : C.owner ≠ C.seed := by
  intro heq
  have hmem := C.owner_mem
  rw [heq] at hmem
  exact C.seed_dangling.1 hmem

def cappedSingletonFold {m : ℕ} (C D : DanglingColumn m) (howner : C.owner = D.owner)
    (hseed : C.seed ≠ D.seed) : Fold tetrahedralLattice (capWord [Residue.H]).length :=
  cappedWordFold (oneHFold C.owner) C.seed D.seed (by decide)
    (fun _ => by change C.seed ≠ C.owner; exact (columnOwner_ne_seed C).symm)
    (fun _ => by change C.owner ≠ D.seed; rw [howner]; exact columnOwner_ne_seed D) hseed
    (fun _ _ => (step_adj C.owner C.dir).symm)
    (fun _ _ => by change tetrahedralLattice.Adj C.owner D.seed; rw [howner]; exact step_adj D.owner D.dir)

def singletonWordPiece {m : ℕ} (C D : DanglingColumn m) (howner : C.owner = D.owner)
    (hseed : C.seed ≠ D.seed) : PositionedWord where
  word := capWord [Residue.H]
  fold := cappedSingletonFold C D howner hseed
  length_pos := by decide
  first := C.seed
  last := D.seed
  first_eq := cappedWordFold_first _ _ _ _ _ _ _ _ _
  last_eq := cappedWordFold_last _ _ _ _ _ _ _ _ _

theorem cappedSingletonFold_hSupport {m : ℕ} (C D : DanglingColumn m)
    (howner : C.owner = D.owner) (hseed : C.seed ≠ D.seed) :
    hSupport (capWord [Residue.H]) (cappedSingletonFold C D howner hseed) = {C.owner} := by
  rw [cappedSingletonFold, cappedWordFold_hSupport, hSupport_oneHFold]

def terminalWordFold (p : ConstructionParameters) : Fold tetrahedralLattice ([Residue.H, .P] : Sequence).length where
  pos i := if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed
  injective_pos i j heq := by
    apply Fin.ext
    have hi : i.val < 2 := i.isLt
    have hj : j.val < 2 := j.isLt
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · omega
    · have he : (terminalColumn p).owner = (terminalColumn p).seed := by
        simpa only [if_pos hi0, if_neg hj0] using heq
      exact False.elim (columnOwner_ne_seed (terminalColumn p) he)
    · have he : (terminalColumn p).owner = (terminalColumn p).seed := by
        simpa only [if_neg hi0, if_pos hj0] using heq.symm
      exact False.elim (columnOwner_ne_seed (terminalColumn p) he)
    · omega
  consecutive i j hij := by
    have hi : i.val < 2 := i.isLt
    have hj : j.val < 2 := j.isLt
    have hi0 : i.val = 0 := by omega
    have hj0 : j.val ≠ 0 := by omega
    simp only [if_pos hi0, if_neg hj0]
    exact step_adj (terminalColumn p).owner (terminalColumn p).dir

def terminalWordPiece (p : ConstructionParameters) : PositionedWord where
  word := [.H, .P]
  fold := terminalWordFold p
  length_pos := by decide
  first := (terminalColumn p).owner
  last := (terminalColumn p).seed
  first_eq i hi := by
    change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) = _
    rw [if_pos hi]
  last_eq i hi := by
    have hi1 : i.val ≠ 0 := by change i.val + 1 = 2 at hi; omega
    change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) = _
    rw [if_neg hi1]

end ProteinFolding.Tetrahedral.NearField
