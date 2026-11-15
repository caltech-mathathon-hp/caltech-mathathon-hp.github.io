import ProteinFolding.Tetrahedral.NearFieldFrameCaps
import ProteinFolding.Tetrahedral.NearFieldFrameSeparation

/-! The two borrowed linker-cap prefixes avoid every prescribed frame link. -/

namespace ProteinFolding.Tetrahedral

def frameLinkerCapCoordinates (m i : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then -1 else if k = 1 then octRadius m + i + 1 else -octRadius m + i - 1

def frameBorrowSecondCoordinates (m i : ℕ) (mode : Bool) (k : Fin 3) : ℤ :=
  if k = 0 then -2 else if k = 1 then octRadius m + i + (if mode then 2 else 0)
  else -octRadius m + i + (if mode then 0 else -2)

theorem frameLinkerCap_coordinates {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) :
    (frameLinkerCap m i).val = frameLinkerCapCoordinates m i := by
  change (step (octEdgeZigzag m entryEdgeFrame i) 2).val = _
  rw [step_val_of_A _ (frameEntryAnchor_inA hm i hi), entryEdgeZigzag_coordinates hm]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [entryEdgeCoordinates, frameLinkerCapCoordinates, bondComponent] <;> omega

theorem frameBorrowSecond_coordinates {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    ((frameBorrowColumn hm i hi hilo hihi mode).point 1).val = frameBorrowSecondCoordinates m i mode := by
  have hcapB : InBSublattice (frameLinkerCap m i).val := step_in_B (frameEntryAnchor_inA hm i hi) 2
  rw [← frameLinkerCap_step hm i hi hilo hihi mode,
    step_val_of_B (frameLinkerCap m i) hcapB, frameLinkerCap_coordinates hm i hi]
  funext k
  rw [bondVector_eq_bondComponent]
  cases mode <;> fin_cases k <;>
    dsimp [frameLinkerCapCoordinates, frameBorrowSecondCoordinates, bondComponent] <;> omega

private theorem initial_cap_offset_ne (r : Fin (nearFrameLength 0)) :
    nearFrameOffset 0 r.val ≠ (fun k => if k = 0 then (-1 : ℤ) else if k = 1 then 3 else 1) := by
  revert r
  decide

private theorem own_slot_cap_offset_ne (r : Fin (nearFrameLength 1)) :
    nearFrameOffset 1 r.val ≠ (fun k => if k = 0 then (-2 : ℤ) else if k = 1 then 2 else 0) := by
  revert r
  decide

private theorem frameCap_ne_initial {m : ℕ} (hm : 1 ≤ m) (q : ℕ) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength 0)) : frameLinkerCap m 2 ≠ nearFramePoint m q 0 hq r := by
  intro heq
  apply initial_cap_offset_ne r
  funext k
  have h := congrArg (fun p : Site => p.val k) heq
  change (frameLinkerCap m 2).val k = (nearFramePoint m q 0 hq r).val k at h
  rw [frameLinkerCap_coordinates hm 2 (by decide)] at h
  change frameLinkerCapCoordinates m 2 k = nearFrameReference m q 0 k + nearFrameOffset 0 r.val k at h
  fin_cases k <;> dsimp [frameLinkerCapCoordinates, nearFrameReference] at h ⊢ <;> omega

private theorem frameCap_ne_own_slot {m : ℕ} (hm : 1 ≤ m) (i q : ℕ) (hi : i % 2 = 0)
    (hq : q % 2 = 1) (hown : q + 1 = i) (r : Fin (nearFrameLength 1)) :
    frameLinkerCap m i ≠ nearFramePoint m q 1 hq r := by
  intro heq
  apply own_slot_cap_offset_ne r
  funext k
  have h := congrArg (fun p : Site => p.val k) heq
  change (frameLinkerCap m i).val k = (nearFramePoint m q 1 hq r).val k at h
  rw [frameLinkerCap_coordinates hm i hi] at h
  change frameLinkerCapCoordinates m i k = nearFrameReference m q 1 k + nearFrameOffset 1 r.val k at h
  fin_cases k <;> dsimp [frameLinkerCapCoordinates, nearFrameReference] at h ⊢ <;> omega

theorem frameLinkerCap_ne_frameP {m : ℕ} (hm : 1 ≤ m) (i q : ℕ) (hi : i % 2 = 0)
    (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hipos : i = 2 ∨ 6 ≤ i) (hindex : (i : ℤ) + 4 ≤ octRadius m)
    (kind : Fin 6) (hslots : kind = 1 → q + 1 = i ∨ q + 6 ≤ i ∨ i + 3 ≤ q)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    frameLinkerCap m i ≠ nearFramePoint m q kind hq r := by
  intro heq
  obtain ⟨hxl, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 0
  obtain ⟨hyl, hyu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 1
  have hx : (nearFramePoint m q kind hq r).val 0 = -1 := by
    rw [← heq, frameLinkerCap_coordinates hm i hi]
    rfl
  have hy : (nearFramePoint m q kind hq r).val 1 = octRadius m + i + 1 := by
    rw [← heq, frameLinkerCap_coordinates hm i hi]
    rfl
  fin_cases kind <;> dsimp only at hxl hxu hyl hyu hx hy
  · rcases hipos with rfl | hipos
    · exact frameCap_ne_initial hm q hq r heq
    · change (nearFramePoint m q 0 hq r).val 1 ≤ octRadius m + 5 at hyu
      change (nearFramePoint m q 0 hq r).val 1 = octRadius m + i + 1 at hy
      omega
  · have hs := hslots rfl
    rcases hs with hown | hlo | hhi
    · exact frameCap_ne_own_slot hm i q hi hq hown r heq
    · change (nearFramePoint m q 1 hq r).val 1 ≤ octRadius m + q + 5 at hyu
      change (nearFramePoint m q 1 hq r).val 1 = octRadius m + i + 1 at hy
      omega
    · change octRadius m + q + 1 ≤ (nearFramePoint m q 1 hq r).val 1 at hyl
      change (nearFramePoint m q 1 hq r).val 1 = octRadius m + i + 1 at hy
      omega
  · change 2 * octRadius m - 1 ≤ (nearFramePoint m q 2 hq r).val 1 at hyl
    change (nearFramePoint m q 2 hq r).val 1 = octRadius m + i + 1 at hy
    omega
  · change 1 ≤ (nearFramePoint m q 3 hq r).val 0 at hxl
    change (nearFramePoint m q 3 hq r).val 0 = -1 at hx
    omega
  · change octRadius m - q - 6 ≤ (nearFramePoint m q 4 hq r).val 0 at hxl
    change (nearFramePoint m q 4 hq r).val 0 = -1 at hx
    omega
  · change octRadius m - 1 ≤ (nearFramePoint m q 5 hq r).val 0 at hxl
    change (nearFramePoint m q 5 hq r).val 0 = -1 at hx
    omega

theorem frameBorrowSecond_ne_frameP {m : ℕ} (hm : 1 ≤ m) (i q : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hindex : (i : ℤ) + 4 ≤ octRadius m) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (frameBorrowColumn hm i hi hilo hihi mode).point 1 ≠ nearFramePoint m q kind hq r := by
  intro heq
  obtain ⟨hxl, hxu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 0
  obtain ⟨hyl, hyu⟩ := nearFramePoint_coordinate_bounds m q kind hq r hr0 hrlast 1
  have hx : (nearFramePoint m q kind hq r).val 0 = -2 := by
    rw [← heq, frameBorrowSecond_coordinates hm i hi hilo hihi mode]
    rfl
  have hy : (nearFramePoint m q kind hq r).val 1 = octRadius m + i + (if mode then 2 else 0) := by
    rw [← heq, frameBorrowSecond_coordinates hm i hi hilo hihi mode]
    rfl
  fin_cases kind
  · change -1 ≤ (nearFramePoint m q 0 hq r).val 0 at hxl
    change (nearFramePoint m q 0 hq r).val 0 = -2 at hx
    omega
  · change -1 ≤ (nearFramePoint m q 1 hq r).val 0 at hxl
    change (nearFramePoint m q 1 hq r).val 0 = -2 at hx
    omega
  · change 2 * octRadius m - 1 ≤ (nearFramePoint m q 2 hq r).val 1 at hyl
    change (nearFramePoint m q 2 hq r).val 1 = octRadius m + i + (if mode then 2 else 0) at hy
    cases mode <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hy <;> omega
  · change 1 ≤ (nearFramePoint m q 3 hq r).val 0 at hxl
    change (nearFramePoint m q 3 hq r).val 0 = -2 at hx
    omega
  · change octRadius m - q - 6 ≤ (nearFramePoint m q 4 hq r).val 0 at hxl
    change (nearFramePoint m q 4 hq r).val 0 = -2 at hx
    omega
  · change octRadius m - 1 ≤ (nearFramePoint m q 5 hq r).val 0 at hxl
    change (nearFramePoint m q 5 hq r).val 0 = -2 at hx
    omega

namespace NearField

theorem frameBorrowPoint_ne_frameP {m : ℕ} (hm : 1 ≤ m) (i q : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hipos : i = 2 ∨ 6 ≤ i) (hindex : (i : ℤ) + 4 ≤ octRadius m)
    (kind : Fin 6) (hslots : kind = 1 → q + 1 = i ∨ q + 6 ≤ i ∨ i + 3 ≤ q)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (n : ℕ) : frameBorrowPoint hm i hi hilo hihi mode n ≠ nearFramePoint m q kind hq r := by
  cases n with
  | zero => exact frameLinkerCap_ne_frameP hm i q hi hq hqlo hqhi hipos hindex kind hslots r hr0 hrlast
  | succ n =>
    cases n with
    | zero => exact frameBorrowSecond_ne_frameP hm i q hi hilo hihi mode hq hqlo hqhi hindex kind r hr0 hrlast
    | succ n =>
      intro heq
      have hc := (frameBorrowColumn hm i hi hilo hihi mode).point_mem_skin (n + 1 + 1)
      have hp := nearFramePoint_mem_skin_one m q kind hq hqlo hqhi r hr0 hrlast
      change (frameBorrowColumn hm i hi hilo hihi mode).point (n + 1 + 1) = _ at heq
      rw [heq] at hc
      exact Finset.disjoint_left.mp (skins_disjoint m 1 ((n + 1 + 1) / 2 + 1) (by omega)) hp hc

end NearField
end ProteinFolding.Tetrahedral
