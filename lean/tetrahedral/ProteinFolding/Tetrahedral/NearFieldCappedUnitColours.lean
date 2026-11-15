import ProteinFolding.Tetrahedral.NearFieldCappedUnitRouting
import ProteinFolding.Tetrahedral.FarFieldParity
import ProteinFolding.Tetrahedral.ConstructionParameters
import ProteinFolding.Tetrahedral.ColumnsSkins

/-! Physical cap colours follow from adjacency to the selected columns,
including when an entry cap is borrowed from a different local owner. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem column_point_one_colour {m : ℕ} (C : DanglingColumn m) :
    FarField.colour (C.point 1) = FarField.colour C.owner := by
  rw [C.point_one_eq]
  have h₁ := FarField.adj_colour (step_adj C.owner C.dir)
  have h₂ := FarField.adj_colour (step_adj C.seed (columnOpposite C.dir))
  change FarField.colour (step C.seed (columnOpposite C.dir)) = FarField.colour C.owner
  rw [h₂]
  change (!FarField.colour (step C.owner C.dir)) = FarField.colour C.owner
  rw [h₁, Bool.not_not]

theorem colour_of_adjacent_to_column_one {m : ℕ} (x : Site) (C : DanglingColumn m)
    (h : tetrahedralLattice.Adj x (C.point 1)) : FarField.colour x = !FarField.colour C.owner := by
  have hc := FarField.adj_colour h
  rw [column_point_one_colour C] at hc
  have hn := congrArg Bool.not hc
  simpa only [Bool.not_not] using hn.symm

def CappedUnit.ownerColours {m : ℕ} (u : CappedUnit m) : Bool × Bool :=
  (FarField.colour u.entry.owner, FarField.colour u.exit.owner)

theorem CappedUnit.first_colour {m : ℕ} (u : CappedUnit m) :
    FarField.colour u.piece.first = !u.ownerColours.1 :=
  colour_of_adjacent_to_column_one u.piece.first u.entry u.first_adjacent

theorem CappedUnit.last_colour {m : ℕ} (u : CappedUnit m) :
    FarField.colour u.piece.last = !u.ownerColours.2 :=
  colour_of_adjacent_to_column_one u.piece.last u.exit u.last_adjacent

theorem CappedUnit.endpoint_colour {m : ℕ} (u : CappedUnit m) (first : Bool) :
    FarField.colour (wordEndpoint u.piece first) = !FarField.colour (u.column first).owner := by
  cases first
  · exact u.last_colour
  · exact u.first_colour

private theorem cap_parity_of_owner_bits (a b c : Bool) (L : ℕ)
    (hc : c = (a == b)) (hL : L % 2 = if c then 1 else 0) :
    (if (!a) = (!b) then L % 2 = 1 else L % 2 = 0) := by
  cases a <;> cases b <;> cases c
  · cases hc
  · exact hL
  · exact hL
  · cases hc
  · exact hL
  · cases hc
  · cases hc
  · exact hL

theorem capParity_longLinker_of_columnOwner_bit {m : ℕ} (p : ConstructionParameters) (w : ℕ)
    (x y : Site) (C D : DanglingColumn m)
    (hx : tetrahedralLattice.Adj x (C.point 1)) (hy : tetrahedralLattice.Adj y (D.point 1))
    (b : Bool) (hb : b = (FarField.colour C.owner == FarField.colour D.owner)) :
    FarField.CapParity x y (p.longLinkerLength w b) := by
  have hcx := colour_of_adjacent_to_column_one x C hx
  have hcy := colour_of_adjacent_to_column_one y D hy
  have hL := p.longLinkerLength_parity w b
  rw [FarField.CapParity, hcx, hcy]
  exact cap_parity_of_owner_bits (FarField.colour C.owner) (FarField.colour D.owner) b
    (p.longLinkerLength w b) hb hL

theorem CappedUnit.linker_capParity {m : ℕ} (u v : CappedUnit m) (p : ConstructionParameters)
    (w : ℕ) (b : Bool) (hb : b = (u.ownerColours.2 == v.ownerColours.1)) :
    FarField.CapParity u.piece.last v.piece.first (p.longLinkerLength w b) :=
  capParity_longLinker_of_columnOwner_bit p w u.piece.last v.piece.first u.exit v.entry
    u.last_adjacent v.first_adjacent b hb

theorem selectedUnitWireColumn_capParity {m n : ℕ} (terminal : PositionedWord)
    (bs : Fin n → CappedUnit m) (C : DanglingColumn m) (hterminal : terminal.last = C.seed)
    (e : FarField.Pairing (2 * n) n) (p : ConstructionParameters) (w : ℕ) (r : Fin n) (b : Bool)
    (hb : b = (FarField.colour (selectedUnitWireColumn bs C e (e.first r)).owner ==
      FarField.colour (selectedUnitWireColumn bs C e (e.second r)).owner)) :
    FarField.CapParity (wireCapSite (cappedRoutingUnits terminal bs) e (e.first r))
      (wireCapSite (cappedRoutingUnits terminal bs) e (e.second r)) (p.longLinkerLength w b) :=
  capParity_longLinker_of_columnOwner_bit p w _ _ _ _
    (selectedUnitWireColumn_adjacent terminal bs C hterminal e (e.first r))
    (selectedUnitWireColumn_adjacent terminal bs C hterminal e (e.second r)) b hb

end ProteinFolding.Tetrahedral.NearField
