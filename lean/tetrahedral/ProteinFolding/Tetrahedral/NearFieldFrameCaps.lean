import ProteinFolding.Tetrahedral.NearFieldFrameBounds
import ProteinFolding.Tetrahedral.ColumnsDisjoint

/-! The two Appendix C borrowed linker-cap geometries on e1. The mode false
is a two-slot anchor; mode true at index2 is the first left-filler cap. -/

namespace ProteinFolding.Tetrahedral

theorem frameEntryAnchor_inA {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) :
    InASublattice (octEdgeZigzag m entryEdgeFrame i).val := by
  have heq : i = 2 * (i / 2) := by omega
  rw [heq]
  exact (octEdgeZigzag_even hm entryEdgeFrame (i / 2)).1

def frameBorrowOffset (mode : Bool) (k : Fin 3) : ℤ :=
  if k = 0 then -2 else if k = 1 then (if mode then 0 else -2) else if mode then 2 else 0

theorem frameBorrowOffset_inA (mode : Bool) : InASublattice (frameBorrowOffset mode) := by
  revert mode
  decide

def frameBorrowOwner {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) (mode : Bool) : Site :=
  ⟨fun k => (octEdgeZigzag m entryEdgeFrame i).val k + frameBorrowOffset mode k,
    Or.inl (near_add_A_A (frameEntryAnchor_inA hm i hi) (frameBorrowOffset_inA mode))⟩

theorem frameBorrowOwner_inA {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) (mode : Bool) :
    InASublattice (frameBorrowOwner hm i hi mode).val :=
  near_add_A_A (frameEntryAnchor_inA hm i hi) (frameBorrowOffset_inA mode)

theorem frameBorrowOwner_mem {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    frameBorrowOwner hm i hi mode ∈ octahedron m := by
  rw [mem_octahedron, inOctahedron_iff_A m (frameBorrowOwner_inA hm i hi mode)]
  intro k
  change -octRadius m ≤ tetraCoordinate m
      (fun a => (octEdgeZigzag m entryEdgeFrame i).val a + frameBorrowOffset mode a) k ∧
    tetraCoordinate m (fun a => (octEdgeZigzag m entryEdgeFrame i).val a + frameBorrowOffset mode a) k ≤ octRadius m
  simp only [tetraCoordinate_add_linear]
  rw [entryEdgeZigzag_coordinates hm]
  cases mode <;> fin_cases k <;>
    dsimp [entryEdgeCoordinates, frameBorrowOffset, tetraCoordinate, octRadius] at hihi ⊢
  all_goals constructor <;> omega

theorem frameBorrowOwner_face {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0) (mode : Bool) :
    tetraCoordinate m (frameBorrowOwner hm i hi mode).val 2 = octRadius m := by
  change tetraCoordinate m (fun a => (octEdgeZigzag m entryEdgeFrame i).val a + frameBorrowOffset mode a) 2 = _
  rw [tetraCoordinate_add_linear, entryEdgeZigzag_coordinates hm]
  cases mode <;> dsimp [entryEdgeCoordinates, frameBorrowOffset, tetraCoordinate, octRadius] <;> omega

def frameBorrowColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) : DanglingColumn m where
  owner := frameBorrowOwner hm i hi mode
  dir := 2
  owner_mem := frameBorrowOwner_mem hm i hi hilo hihi mode
  seed_outside := (step_not_mem_octahedron_A m (frameBorrowOwner_inA hm i hi mode)
    (frameBorrowOwner_mem hm i hi hilo hihi mode) 2).mpr (frameBorrowOwner_face hm i hi mode)

def frameLinkerCap (m i : ℕ) : Site := step (octEdgeZigzag m entryEdgeFrame i) 2

theorem frameLinkerCap_dangling {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (_hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) : IsDangling m (frameLinkerCap m i) := by
  have hrange : i < 2 * m - 1 := by dsimp [octRadius] at hihi; omega
  have he := octEdgeZigzag_mem hm entryEdgeFrame hrange
  have ho : octEdgeZigzag m entryEdgeFrame i ∈ octahedron m :=
    he.elim (fun h => h.1.1) (fun h => h.1.1)
  have hpA := frameEntryAnchor_inA hm i hi
  have hface : tetraCoordinate m (octEdgeZigzag m entryEdgeFrame i).val 2 = octRadius m := by
    rw [entryEdgeZigzag_coordinates hm]
    dsimp [entryEdgeCoordinates, tetraCoordinate]
    omega
  exact ⟨(step_not_mem_octahedron_A m hpA ho 2).mpr hface, _, ho, step_adj _ _⟩

theorem frameLinkerCap_step {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    step (frameLinkerCap m i) (if mode then 1 else 0) =
      (frameBorrowColumn hm i hi hilo hihi mode).point 1 := by
  have hpA := frameEntryAnchor_inA hm i hi
  have hvA := frameBorrowOwner_inA hm i hi mode
  rw [(frameBorrowColumn hm i hi hilo hihi mode).point_one_eq]
  apply Subtype.ext
  change (step (step (octEdgeZigzag m entryEdgeFrame i) 2) (if mode then 1 else 0)).val =
    (step (step (frameBorrowOwner hm i hi mode) 2) 3).val
  rw [step_val_of_B _ (step_in_B hpA 2), step_val_of_A _ hpA,
    step_val_of_B _ (step_in_B hvA 2), step_val_of_A _ hvA]
  simp_rw [bondVector_eq_bondComponent]
  funext k
  cases mode <;> fin_cases k <;> dsimp [frameBorrowOwner, frameBorrowOffset, bondComponent] <;> omega

theorem frameBorrow_seed_ne_cap {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    (frameBorrowColumn hm i hi hilo hihi mode).seed ≠ frameLinkerCap m i := by
  intro heq
  have h := congrArg (fun p : Site => step p 2) heq
  change step (step (frameBorrowOwner hm i hi mode) 2) 2 =
    step (step (octEdgeZigzag m entryEdgeFrame i) 2) 2 at h
  rw [step_step, step_step] at h
  have hx := congrArg (fun p : Site => p.val 0) h
  change (octEdgeZigzag m entryEdgeFrame i).val 0 + (-2) =
    (octEdgeZigzag m entryEdgeFrame i).val 0 at hx
  omega

theorem frameLinkerCap_not_in_borrowed_column {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    frameLinkerCap m i ∉ (frameBorrowColumn hm i hi hilo hihi mode).sites := by
  rintro ⟨n, heq⟩
  have hdang : IsDangling m ((frameBorrowColumn hm i hi hilo hihi mode).point n) := by
    rw [heq]
    exact frameLinkerCap_dangling hm i hi hilo hihi
  have hn := ((frameBorrowColumn hm i hi hilo hihi mode).point_dangling_iff_zero n).mp hdang
  subst n
  exact frameBorrow_seed_ne_cap hm i hi hilo hihi mode heq

namespace NearField

def frameBorrowPoint {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) : ℕ → Site
  | 0 => frameLinkerCap m i
  | n + 1 => (frameBorrowColumn hm i hi hilo hihi mode).point (n + 1)

theorem frameBorrowPoint_adj {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) :
    tetrahedralLattice.Adj (frameBorrowPoint hm i hi hilo hihi mode n)
      (frameBorrowPoint hm i hi hilo hihi mode (n + 1)) := by
  cases n with
  | zero =>
    change tetrahedralLattice.Adj (frameLinkerCap m i) ((frameBorrowColumn hm i hi hilo hihi mode).point 1)
    rw [← frameLinkerCap_step hm i hi hilo hihi mode]
    exact step_adj _ _
  | succ n => exact (frameBorrowColumn hm i hi hilo hihi mode).point_adj (n + 1)

theorem frameBorrowPoint_injective {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) :
    Function.Injective (frameBorrowPoint hm i hi hilo hihi mode) := by
  intro n k h
  cases n with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact False.elim (frameLinkerCap_not_in_borrowed_column hm i hi hilo hihi mode ⟨k + 1, h.symm⟩)
  | succ n =>
    cases k with
    | zero => exact False.elim (frameLinkerCap_not_in_borrowed_column hm i hi hilo hihi mode ⟨n + 1, h⟩)
    | succ k => exact (frameBorrowColumn hm i hi hilo hihi mode).point_injective h

theorem frameBorrowPoint_outside {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) :
    frameBorrowPoint hm i hi hilo hihi mode n ∉ octahedron m := by
  cases n with
  | zero => exact (frameLinkerCap_dangling hm i hi hilo hihi).1
  | succ n => exact (frameBorrowColumn hm i hi hilo hihi mode).point_outside (n + 1)

def frameBorrowPrefixFold {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool) (n : ℕ) : Fold tetrahedralLattice n where
  pos j := frameBorrowPoint hm i hi hilo hihi mode j.val
  injective_pos := fun _ _ h => Fin.ext (frameBorrowPoint_injective hm i hi hilo hihi mode h)
  consecutive j k hjk := by rw [← hjk]; exact frameBorrowPoint_adj hm i hi hilo hihi mode j.val

end NearField
end ProteinFolding.Tetrahedral
