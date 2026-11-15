import ProteinFolding.Tetrahedral.ReductionWordCounts

/-! The exact long-linker lengths, with both endpoint caps counted. -/

namespace ProteinFolding.Tetrahedral

theorem capped_words_merge_P_run (u v : Sequence) (n : ℕ) :
    capWord u ++ List.replicate n .P ++ capWord v =
      .P :: (u ++ List.replicate (n + 2) .P ++ v ++ [.P]) := by
  have hrep : [Residue.P] ++ List.replicate n Residue.P ++ [Residue.P] =
      List.replicate (n + 2) Residue.P := by
    change List.replicate 1 Residue.P ++ List.replicate n Residue.P ++
      List.replicate 1 Residue.P = _
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  simp only [capWord, List.cons_append, List.append_assoc]
  have h := congrArg (fun w : Sequence => .P :: (u ++ w ++ v ++ [.P])) hrep
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

namespace ConstructionParameters

def reductionWireCount (p : ConstructionParameters) (items bulkLengths : List ℕ) : ℕ :=
  2 * (p.reductionUnitBodies items bulkLengths).length

theorem reductionWireCount_eq (p : ConstructionParameters) (items bulkLengths : List ℕ) :
    p.reductionWireCount items bulkLengths =
      2 * (p.bins + items.length + bulkLengths.length + 10) := by
  rw [reductionWireCount, reductionUnitBodies_length]

/-- The finite parity list records whether the two neighbouring H endpoints
lie on the same sublattice; its construction remains a geometric obligation. -/
def prescribedLinkerGap (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (sameSublattice : List Bool) (i : ℕ) : ℕ :=
  p.longLinkerLength (p.reductionWireCount items bulkLengths)
    (sameSublattice[i]?.getD false) - 2

theorem prescribedLinkerGap_add_two (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (sameSublattice : List Bool) (i : ℕ) :
    p.prescribedLinkerGap items bulkLengths sameSublattice i + 2 =
      p.longLinkerLength (p.reductionWireCount items bulkLengths)
        (sameSublattice[i]?.getD false) := by
  unfold prescribedLinkerGap longLinkerLength baseLinkerLength
  omega

def prescribedReductionWord (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (sameSublattice : List Bool) : Sequence :=
  p.reductionWord items bulkLengths (p.prescribedLinkerGap items bulkLengths sameSublattice)

theorem prescribedReductionWord_phpIndices_card (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (sameSublattice : List Bool)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (phpIndices (p.prescribedReductionWord items bulkLengths sameSublattice)).card = 6 :=
  p.reductionWord_phpIndices_card items bulkLengths _ hbulk

theorem prescribedReductionWord_hydrophobicCount (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (sameSublattice : List Bool)
    (htotal : items.sum = p.bins * p.capacity)
    (hbulk : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42) :
    hydrophobicCount (p.prescribedReductionWord items bulkLengths sameSublattice) = octahedralNumber p.side :=
  p.reductionWord_hydrophobicCount items bulkLengths _ htotal hbulk

end ConstructionParameters

end ProteinFolding.Tetrahedral
