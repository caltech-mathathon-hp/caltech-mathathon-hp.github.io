import ProteinFolding.Tetrahedral.NearFieldFrameCapSeparation

/-! Borrowed linker-cap prefixes stay strictly on the negative-x side of F'. -/

namespace ProteinFolding.Tetrahedral

theorem frameBorrowColumn_sy {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    (frameBorrowColumn hm i hi hilo hihi mode).sy = 1 := by
  change (if InASublattice (frameBorrowOwner hm i hi mode).val then bigFaceY 2 else -bigFaceY 2) = 1
  rw [if_pos (frameBorrowOwner_inA hm i hi mode)]
  rfl

theorem frameBorrowColumn_sz {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    (frameBorrowColumn hm i hi hilo hihi mode).sz = -1 := by
  change (if InASublattice (frameBorrowOwner hm i hi mode).val then bigFaceZ 2 else -bigFaceZ 2) = -1
  rw [if_pos (frameBorrowOwner_inA hm i hi mode)]
  rfl

theorem frameBorrowColumn_seed_x {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    (frameBorrowColumn hm i hi hilo hihi mode).seed.val 0 = -3 := by
  change (step (frameBorrowOwner hm i hi mode) 2).val 0 = -3
  rw [step_val_of_A _ (frameBorrowOwner_inA hm i hi mode)]
  change (frameBorrowOwner hm i hi mode).val 0 + bondVector 2 0 = -3
  rw [bondVector_eq_bondComponent]
  change (octEdgeZigzag m entryEdgeFrame i).val 0 + frameBorrowOffset mode 0 + bondComponent 2 0 = -3
  rw [entryEdgeZigzag_coordinates hm]
  dsimp [entryEdgeCoordinates, frameBorrowOffset, bondComponent]
  omega

theorem frameBorrowColumn_negativeX {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) :
    ((frameBorrowColumn hm i hi hilo hihi mode).point n).val 0 ≤ -2 := by
  let C := frameBorrowColumn hm i hi hilo hihi mode
  have hx := bulkArmPoint_x_charge C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hsB : InBSublattice C.seed.val := step_in_B (frameBorrowOwner_inA hm i hi mode) 2
  have hscharge := siteCharge_B hsB
  have hc := siteCharge_bounds (C.point n)
  change (C.point n).val 0 = C.seed.val 0 + (siteCharge (C.point n) - siteCharge C.seed) * (C.sy * C.sz) at hx
  have hsy : C.sy = 1 := frameBorrowColumn_sy hm i hi hilo hihi mode
  have hsz : C.sz = -1 := frameBorrowColumn_sz hm i hi hilo hihi mode
  have hsx : C.seed.val 0 = -3 := frameBorrowColumn_seed_x hm i hi hilo hihi mode
  rw [hsy, hsz, hscharge, hsx] at hx
  change (C.point n).val 0 ≤ -2
  omega

theorem NearField.frameBorrowPoint_negativeX {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) :
    (NearField.frameBorrowPoint hm i hi hilo hihi mode n).val 0 ≤ -1 := by
  cases n with
  | zero =>
    change (frameLinkerCap m i).val 0 ≤ -1
    rw [frameLinkerCap_coordinates hm i hi]
    exact le_refl (-1)
  | succ n =>
    have h := frameBorrowColumn_negativeX hm i hi hilo hihi mode (n + 1)
    exact le_trans h (by decide)

end ProteinFolding.Tetrahedral
