import ProteinFolding.Tetrahedral.NearFieldSeparatorChainSeparation
import ProteinFolding.Tetrahedral.NearFieldSeparatorWordClearance
import ProteinFolding.Tetrahedral.NearFieldWordFoldAppend

/-! The complete, literal separator word is one actual self-avoiding fold. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def separatorEntryWalkWord (p : ConstructionParameters) (k : ℕ) : Sequence :=
  dimerChain 1 ++ List.replicate (p.entryTether k) .P

def separatorMiddleWord (p : ConstructionParameters) (k : ℕ) : Sequence :=
  separatorEntryWalkWord p k ++ dimerChain 2

def separatorMiddleOutWord (p : ConstructionParameters) (k : ℕ) : Sequence :=
  separatorMiddleWord p k ++ List.replicate (p.exitTether k) .P

def separatorEntryWalk (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (separatorEntryWalkWord p k).length :=
  Fold.appendWord (separatorEntryChain p k hk) (entryTetherWordFold p k hk)
    (separatorEntry_ne_entryWord p k k hk hk)
    (by
      intro i j hi hj
      rw [separatorEntryChain_last p k hk i hi, entryTetherWordFold_first p k hk j hj]
      exact step_adj _ _)

theorem separatorEntryWalk_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hA : ∀ i, P ((separatorEntryChain p k hk).pos i))
    (hB : ∀ i, P ((entryTetherWordFold p k hk).pos i)) (i : Fin (separatorEntryWalkWord p k).length) :
    P ((separatorEntryWalk p k hk).pos i) := appendWord_property _ _ _ _ P hA hB i

theorem separatorEntryWalk_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorEntryWalkWord p k).length) (hi : i.val + 1 = (separatorEntryWalkWord p k).length) :
    (separatorEntryWalk p k hk).pos i = (entryTargetColumn p k hk).seed :=
  appendWord_last _ _ _ _ (entryTetherWordFold_length_pos p k) _ (entryTetherWordFold_last p k hk) i hi

def separatorMiddle (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (separatorMiddleWord p k).length :=
  Fold.appendWord (separatorEntryWalk p k hk) (separatorCenterChain p k hk)
    (fun i j => separatorEntryWalk_property p k hk (fun x => x ≠ (separatorCenterChain p k hk).pos j)
      (fun r => separatorEntry_center_disjoint p k k hk hk r j)
      (fun r => (separatorCenter_ne_entryWord p k k hk hk j r).symm) i)
    (by
      intro i j hi hj
      rw [separatorEntryWalk_last p k hk i hi, separatorCenterChain_first p k hk j hj]
      exact (step_adj _ _).symm)

theorem separatorMiddle_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hA : ∀ i, P ((separatorEntryChain p k hk).pos i))
    (hB : ∀ i, P ((entryTetherWordFold p k hk).pos i))
    (hC : ∀ i, P ((separatorCenterChain p k hk).pos i)) (i : Fin (separatorMiddleWord p k).length) :
    P ((separatorMiddle p k hk).pos i) :=
  appendWord_property _ _ _ _ P (separatorEntryWalk_property p k hk P hA hB) hC i

theorem separatorMiddle_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorMiddleWord p k).length) (hi : i.val + 1 = (separatorMiddleWord p k).length) :
    (separatorMiddle p k hk).pos i = (exitSourceColumn p k hk).owner :=
  appendWord_last _ _ _ _ (by decide : 0 < (dimerChain 2).length) _ (separatorCenterChain_last p k hk) i hi

def separatorMiddleOut (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (separatorMiddleOutWord p k).length :=
  Fold.appendWord (separatorMiddle p k hk) (exitTetherWordFold p k hk)
    (fun i j => separatorMiddle_property p k hk (fun x => x ≠ (exitTetherWordFold p k hk).pos j)
      (fun r => separatorEntry_ne_exitWord p k k hk hk r j)
      (fun r => entryWord_ne_exitWord p k k hk hk r j)
      (fun r => separatorCenter_ne_exitWord p k k hk hk r j) i)
    (by
      intro i j hi hj
      rw [separatorMiddle_last p k hk i hi, exitTetherWordFold_first p k hk j hj]
      exact step_adj _ _)

theorem separatorMiddleOut_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hA : ∀ i, P ((separatorEntryChain p k hk).pos i))
    (hB : ∀ i, P ((entryTetherWordFold p k hk).pos i))
    (hC : ∀ i, P ((separatorCenterChain p k hk).pos i))
    (hD : ∀ i, P ((exitTetherWordFold p k hk).pos i)) (i : Fin (separatorMiddleOutWord p k).length) :
    P ((separatorMiddleOut p k hk).pos i) :=
  appendWord_property _ _ _ _ P (separatorMiddle_property p k hk P hA hB hC) hD i

theorem separatorMiddleOut_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorMiddleOutWord p k).length) (hi : i.val + 1 = (separatorMiddleOutWord p k).length) :
    (separatorMiddleOut p k hk).pos i = (exitTargetColumn p k).seed :=
  appendWord_last _ _ _ _ (exitTetherWordFold_length_pos p k) _ (exitTetherWordFold_last p k hk) i hi

def separatorFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (p.separatorWord k).length :=
  Fold.appendWord (separatorMiddleOut p k hk) (separatorExitChain p k)
    (fun i j => separatorMiddleOut_property p k hk (fun x => x ≠ (separatorExitChain p k).pos j)
      (fun r => separatorEntry_exit_disjoint p k k hk r j)
      (fun r => (separatorExit_ne_entryWord p k k hk j r).symm)
      (fun r => separatorCenter_exit_disjoint p k k hk r j)
      (fun r => (separatorExit_ne_exitWord p k k hk j r).symm) i)
    (by
      intro i j hi hj
      rw [separatorMiddleOut_last p k hk i hi, separatorExitChain_first p k j hj]
      exact (step_adj _ _).symm)

theorem separatorFold_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hA : ∀ i, P ((separatorEntryChain p k hk).pos i))
    (hB : ∀ i, P ((entryTetherWordFold p k hk).pos i))
    (hC : ∀ i, P ((separatorCenterChain p k hk).pos i))
    (hD : ∀ i, P ((exitTetherWordFold p k hk).pos i))
    (hE : ∀ i, P ((separatorExitChain p k).pos i)) (i : Fin (p.separatorWord k).length) :
    P ((separatorFold p k hk).pos i) :=
  appendWord_property _ _ _ _ P (separatorMiddleOut_property p k hk P hA hB hC hD) hE i

end ProteinFolding.Tetrahedral.NearField
