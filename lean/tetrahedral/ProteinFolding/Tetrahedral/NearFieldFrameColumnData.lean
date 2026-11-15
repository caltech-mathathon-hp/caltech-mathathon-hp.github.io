import ProteinFolding.Tetrahedral.NearFieldFrameData

/-! Coordinates of an owner recovered from either of the first two column sites. -/

namespace ProteinFolding.Tetrahedral

def nearFrameColumnOwnerCoordinates (m q : ℕ) (kind : Fin 6) (r : ℕ)
    (second ownerA : Bool) (d : Fin 4) (k : Fin 3) : ℤ :=
  nearFrameCoordinates m q kind r k -
    (if ownerA then bondComponent d k else -bondComponent d k) +
    (if second then (if ownerA then bondComponent (columnOpposite d) k else -bondComponent (columnOpposite d) k) else 0)

def nearFrameColumnOtherFace (kind : Fin 6) (second : Bool) (d : Fin 4) : Fin 4 :=
  if kind = 2 ∧ second = true then 1
  else if kind = 0 ∨ kind = 1 then if d = 3 then 2 else 3
  else if kind = 4 then if d = 3 then 0 else 3
  else 3

end ProteinFolding.Tetrahedral

