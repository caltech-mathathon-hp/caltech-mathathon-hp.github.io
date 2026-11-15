import ProteinFolding.Tetrahedral.NearFieldFrameLinkFamily
import ProteinFolding.Tetrahedral.NearFieldFrameTetherHalfspaces
import ProteinFolding.Tetrahedral.NearFieldPPPBorrowedFrameColumns
import ProteinFolding.Tetrahedral.NearFieldBorrowedBulkClearance
import ProteinFolding.Tetrahedral.NearFieldNonbulkEndpointColours
import ProteinFolding.Tetrahedral.NearFieldFrameCapColumns
import ProteinFolding.Tetrahedral.NearFieldTrackAColumns

/-! The selected borrowed columns for the left-filler entry cap and every
separator entry cap, including their actual distinct dangling cap sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

abbrev EntryCapIndex (p : ConstructionParameters) := Option (Fin (p.bins + 1))

def entryCapIndex (p : ConstructionParameters) : EntryCapIndex p → ℕ
  | none => 2
  | some k => 6 * (k.val + 1)

def entryCapMode {p : ConstructionParameters} : EntryCapIndex p → Bool
  | none => true
  | some _ => false

theorem entryCapIndex_even (p : ConstructionParameters) (i : EntryCapIndex p) : entryCapIndex p i % 2 = 0 := by
  cases i <;> dsimp [entryCapIndex] <;> omega

theorem entryCapIndex_lo (p : ConstructionParameters) (i : EntryCapIndex p) : 2 ≤ entryCapIndex p i := by
  cases i <;> dsimp [entryCapIndex] <;> omega

theorem entryCapIndex_room (p : ConstructionParameters) (i : EntryCapIndex p) :
    (entryCapIndex p i : ℤ) + 4 ≤ octRadius p.side := by
  have hm := p.side_ge
  have hf := p.family_side_bound
  cases i with
  | none => dsimp [entryCapIndex, octRadius]; omega
  | some k => have hk := k.isLt; dsimp [entryCapIndex, octRadius]; omega

theorem entryCapIndex_position (p : ConstructionParameters) (i : EntryCapIndex p) :
    entryCapIndex p i = 2 ∨ 6 ≤ entryCapIndex p i := by
  cases i <;> dsimp [entryCapIndex] <;> omega

theorem entryCapIndex_near (p : ConstructionParameters) (i : EntryCapIndex p) :
    entryCapMode i = true ∨ 4 ≤ entryCapIndex p i := by
  cases i with
  | none => exact Or.inl rfl
  | some k => exact Or.inr (by change 4 ≤ 6 * (k.val + 1); omega)

theorem entryCapIndex_separated (p : ConstructionParameters) (i j : EntryCapIndex p) (hne : i ≠ j) :
    entryCapIndex p i + 4 ≤ entryCapIndex p j ∨ entryCapIndex p j + 4 ≤ entryCapIndex p i := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hne rfl)
    | some k => dsimp [entryCapIndex]; omega
  | some k =>
    cases j with
    | none => dsimp [entryCapIndex]; omega
    | some l =>
      have hkl : k.val ≠ l.val := by intro heq; exact hne (congrArg some (Fin.ext heq))
      dsimp [entryCapIndex]
      omega

theorem entryCapIndex_slotCompatible (p : ConstructionParameters) (i : EntryCapIndex p) (q : ℕ)
    (hq : q % 6 = 5) (hlo : 5 ≤ q) :
    q + 1 = entryCapIndex p i ∨ q + 6 ≤ entryCapIndex p i ∨ entryCapIndex p i + 3 ≤ q := by
  cases i <;> dsimp [entryCapIndex] <;> omega

def entryCapSite (p : ConstructionParameters) (i : EntryCapIndex p) : Site :=
  frameLinkerCap p.side (entryCapIndex p i)

def selectedEntryColumn (p : ConstructionParameters) (i : EntryCapIndex p) : DanglingColumn p.side :=
  frameBorrowColumn (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i) (entryCapIndex_even p i)
    (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega) (entryCapMode i)

theorem selectedEntryColumn_seeds_ne (p : ConstructionParameters) (i j : EntryCapIndex p) (hne : i ≠ j) :
    (selectedEntryColumn p i).seed ≠ (selectedEntryColumn p j).seed :=
  frameBorrowColumns_seed_ne (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i) (entryCapIndex p j) (entryCapIndex_even p i)
    (entryCapIndex_even p j) (entryCapIndex_lo p i) (entryCapIndex_lo p j)
    (by have h := entryCapIndex_room p i; omega) (by have h := entryCapIndex_room p j; omega)
    (entryCapMode i) (entryCapMode j) (entryCapIndex_separated p i j hne)

theorem entryCapSite_injective (p : ConstructionParameters) : Function.Injective (entryCapSite p) := by
  intro i j heq
  by_contra hne
  have hs := entryCapIndex_separated p i j hne
  have he := congrArg (fun s => step s 2) heq
  change step (step (octEdgeZigzag p.side entryEdgeFrame (entryCapIndex p i)) 2) 2 =
    step (step (octEdgeZigzag p.side entryEdgeFrame (entryCapIndex p j)) 2) 2 at he
  rw [step_step, step_step] at he
  have hi := octEdgeZigzag_injective (by have h := p.side_ge; omega : 1 ≤ p.side) entryEdgeFrame he
  omega

theorem entryCapSite_dangling (p : ConstructionParameters) (i : EntryCapIndex p) :
    IsDangling p.side (entryCapSite p i) :=
  frameLinkerCap_dangling (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i) (entryCapIndex_even p i)
    (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega)

theorem entryCapSite_adj_columnOne (p : ConstructionParameters) (i : EntryCapIndex p) :
    tetrahedralLattice.Adj (entryCapSite p i) ((selectedEntryColumn p i).point 1) := by
  change tetrahedralLattice.Adj (frameLinkerCap p.side (entryCapIndex p i))
    ((frameBorrowColumn (m := p.side) (by have h := p.side_ge; omega)
      (entryCapIndex p i) (entryCapIndex_even p i) (entryCapIndex_lo p i)
      (by have h := entryCapIndex_room p i; omega) (entryCapMode i)).point 1)
  rw [← frameLinkerCap_step (m := p.side) (by have h := p.side_ge; omega : 1 ≤ p.side) (entryCapIndex p i) (entryCapIndex_even p i)
    (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega) (entryCapMode i)]
  exact step_adj _ _

theorem selectedEntryColumn_owner_colour (p : ConstructionParameters) (i : EntryCapIndex p) :
    FarField.colour (selectedEntryColumn p i).owner = true :=
  ownerColour_A (frameBorrowOwner_inA (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i) (entryCapIndex_even p i) (entryCapMode i))

theorem selectedEntryColumn_ne_frameP (p : ConstructionParameters) (i : EntryCapIndex p) (j : FrameLinkIndex p)
    (n : ℕ) (hn : 1 ≤ n) (s : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (selectedEntryColumn p i).point n ≠ (frameLinkFold p j).pos s := by
  cases n with
  | zero => omega
  | succ n =>
    exact frameBorrowPoint_ne_frameP (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i) (frameLinkParameter j) (entryCapIndex_even p i)
      (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega) (entryCapMode i)
      (frameLinkParameter_odd p j) (frameLinkParameter_ge p j) (frameLinkParameter_room p j)
      (entryCapIndex_position p i) (entryCapIndex_room p i) (frameLinkKind j)
      (fun hj => entryCapIndex_slotCompatible p i _ (frameLink_entry_residue p j hj) (frameLinkParameter_ge p j))
      ⟨s.val + 1, by have h := s.isLt; omega⟩ (by change 0 < s.val + 1; omega)
      (by change s.val + 1 + 1 < nearFrameLength (frameLinkKind j); have h := s.isLt; omega) (n + 1)

theorem edgePPPFold_ne_selectedEntryColumn (p : ConstructionParameters) (i : EntryCapIndex p)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (s : Fin 3) (n : ℕ) (hn : 1 ≤ n) :
    (edgePPPFold p.side F r).pos s ≠ (selectedEntryColumn p i).point n := by
  cases n with
  | zero => omega
  | succ n =>
    exact edgePPPFold_ne_frameBorrowPoint p.side (by have h := p.side_ge; omega) (entryCapIndex p i) (entryCapIndex_even p i)
      (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega) (entryCapMode i)
      (entryCapIndex_near p i) (Or.inr (entryCapIndex_room p i)) F r hr hpair s (n + 1)

theorem selectedEntryColumn_negativeX (p : ConstructionParameters) (i : EntryCapIndex p) (n : ℕ) :
    ((selectedEntryColumn p i).point n).val 0 ≤ -2 :=
  frameBorrowColumn_negativeX (m := p.side) (by have h := p.side_ge; omega)
    (entryCapIndex p i) (entryCapIndex_even p i) (entryCapIndex_lo p i)
    (by have h := entryCapIndex_room p i; omega) (entryCapMode i) n

theorem selectedEntryColumn_positiveY (p : ConstructionParameters) (i : EntryCapIndex p) (n : ℕ) :
    1 + (n : ℤ) ≤ bulkY p.side ((selectedEntryColumn p i).point n) := by
  have h := (selectedEntryColumn p i).point_signed_y n
  have hsy : (selectedEntryColumn p i).sy = 1 :=
    frameBorrowColumn_sy (m := p.side) (by have h := p.side_ge; omega)
      (entryCapIndex p i) (entryCapIndex_even p i) (entryCapIndex_lo p i)
      (by have h := entryCapIndex_room p i; omega) (entryCapMode i)
  rw [hsy, one_mul] at h
  exact h

theorem FacePositive.ne_selectedEntryColumn {p : ConstructionParameters} {s : Site}
    (hs : FacePositive p.side s) (i : EntryCapIndex p) (n : ℕ) :
    s ≠ (selectedEntryColumn p i).point n := by
  intro heq
  have hx := selectedEntryColumn_negativeX p i n
  rw [← heq] at hx
  have h := hs.1
  omega

theorem entryTetherFold_ne_selectedEntryColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : EntryCapIndex p) (n : ℕ) (s : Fin (p.entryTether k)) :
    (entryTetherFold p k hk).pos s ≠ (selectedEntryColumn p i).point n :=
  (entryTetherFold_positive p k hk s).ne_selectedEntryColumn i n

theorem exitTetherFold_ne_selectedEntryColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : EntryCapIndex p) (n : ℕ) (s : Fin (p.exitTether k)) :
    (exitTetherFold p k hk).pos s ≠ (selectedEntryColumn p i).point n :=
  (exitTetherFold_positive p k hk s).ne_selectedEntryColumn i n

theorem selectedEntryColumn_ne_frameEndpointColumn (p : ConstructionParameters) (i : EntryCapIndex p)
    (b : Bool) (n r : ℕ) : (selectedEntryColumn p i).point n ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).point r := by
  intro heq
  have hp := selectedEntryColumn_positiveY p i n
  have hn := frameEndpointColumn_negativeY (m := p.side) (by have h := p.side_ge; omega) b r
  rw [heq] at hp
  omega

theorem selectedEntryColumn_ne_trackAColumn (p : ConstructionParameters) (i : EntryCapIndex p)
    (a : ℕ) (ha : a < p.side) (n r : ℕ) : (selectedEntryColumn p i).point n ≠
      (trackAColumn (m := p.side) (by have h := p.side_ge; omega) a ha).point r := by
  intro heq
  have hp := selectedEntryColumn_positiveY p i n
  have hn := trackAColumn_negativeY (m := p.side) (by have h := p.side_ge; omega) a ha r
  rw [heq] at hp
  omega

end ProteinFolding.Tetrahedral.NearField
