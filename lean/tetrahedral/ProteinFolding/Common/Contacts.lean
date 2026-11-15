import ProteinFolding.Common.Statement

/-! Non-backbone contact scoring, shared independently of the lattice dimension.
Berger--Leighton's `bondCount` includes backbone bonds; `contactCount` excludes
them, following Crescenzi et al. No conversion of thresholds is assumed here. -/

namespace ProteinFolding

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Unordered H-H lattice contacts between nonconsecutive sequence positions.
The order i < j is already imposed by `hhBonds`. -/
def hhContacts (S : Sequence) (f : Fold G S.length) :
    Finset (Fin S.length × Fin S.length) :=
  (hhBonds S f).filter fun ij => ij.1.val + 1 ≠ ij.2.val

def contactCount (S : Sequence) (f : Fold G S.length) : ℕ :=
  (hhContacts S f).card

theorem contactCount_le_bondCount (S : Sequence) (f : Fold G S.length) :
    contactCount S f ≤ bondCount S f :=
  Finset.card_le_card (Finset.filter_subset _ _)

end ProteinFolding
