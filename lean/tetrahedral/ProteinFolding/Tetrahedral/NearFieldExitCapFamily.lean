import ProteinFolding.Tetrahedral.NearFieldTrackAColumns
import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns
import ProteinFolding.Tetrahedral.NearFieldFrameLinkFamily
import ProteinFolding.Tetrahedral.NearFieldFrameCapColumns
import ProteinFolding.Tetrahedral.FarFieldParity

/-! The actual A-owned cap columns at the ends of the separator exit edges. -/

namespace ProteinFolding.Tetrahedral.NearField

def exitAColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) : DanglingColumn m where
  owner := octEdgeZigzag m exitEdgeFrame (2 * i)
  dir := 0
  owner_mem := by
    rcases octEdgeZigzag_mem hm exitEdgeFrame (show 2 * i < 2 * m - 1 by omega) with h | h <;>
      exact h.1.1
  seed_outside := by
    have h := octEdgeZigzag_even hm exitEdgeFrame i
    have hoct : octEdgeZigzag m exitEdgeFrame (2 * i) ∈ octahedron m := by
      rcases octEdgeZigzag_mem hm exitEdgeFrame (show 2 * i < 2 * m - 1 by omega) with h | h <;>
        exact h.1.1
    exact (step_not_mem_octahedron_A m h.1 hoct 0).mpr h.2.1

theorem exitAColumn_sy {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) :
    (exitAColumn hm i hi).sy = 1 := by
  change (if InASublattice (octEdgeZigzag m exitEdgeFrame (2 * i)).val then bigFaceY 0 else -bigFaceY 0) = 1
  rw [if_pos (octEdgeZigzag_even hm exitEdgeFrame i).1]
  rfl

theorem exitAColumn_sz {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) :
    (exitAColumn hm i hi).sz = 1 := by
  change (if InASublattice (octEdgeZigzag m exitEdgeFrame (2 * i)).val then bigFaceZ 0 else -bigFaceZ 0) = 1
  rw [if_pos (octEdgeZigzag_even hm exitEdgeFrame i).1]
  rfl

theorem exitAColumn_seed_coordinates {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m)
    (d : Fin 3) : (exitAColumn hm i hi).seed.val d =
      if d = 0 then octRadius m - 2 * (i : ℤ) + 1
      else if d = 1 then octRadius m + 2 * (i : ℤ) + 1 else 1 := by
  change (step (octEdgeZigzag m exitEdgeFrame (2 * i)) 0).val d = _
  rw [step_val_of_A _ (octEdgeZigzag_even hm exitEdgeFrame i).1]
  change (octEdgeZigzag m exitEdgeFrame (2 * i)).val d + bondVector 0 d = _
  rw [exitEdgeZigzag_coordinates hm, bondVector_eq_bondComponent]
  fin_cases d <;> dsimp [exitEdgeCoordinates, bondComponent] <;> omega

theorem exitAColumn_point_coordinates {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m)
    (n : ℕ) (d : Fin 3) : ((exitAColumn hm i hi).point n).val d =
      if d = 0 then octRadius m - 2 * (i : ℤ) + 1 - (n % 2 : ℕ)
      else if d = 1 then octRadius m + 2 * (i : ℤ) + 1 + n else 1 + n := by
  let C := exitAColumn hm i hi
  have hx := bulkArmPoint_x_charge C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hy := bulkArmPoint_y m C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hz := bulkArmPoint_z C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hsB : InBSublattice C.seed.val := step_in_B (octEdgeZigzag_even hm exitEdgeFrame i).1 0
  have hc0 := siteCharge_B hsB
  have hcn := bulkArmPoint_charge C.sy C.sz C.seed n
  change siteCharge (C.point n) = (if n % 2 = 0 then siteCharge C.seed else 1 - siteCharge C.seed) at hcn
  rw [hc0] at hcn
  have hc : siteCharge (C.point n) = 1 - (n % 2 : ℕ) := by split_ifs at hcn <;> omega
  change (C.point n).val 0 = C.seed.val 0 +
    (siteCharge (C.point n) - siteCharge C.seed) * (C.sy * C.sz) at hx
  change (C.point n).val 1 - octRadius m = C.seed.val 1 - octRadius m + (n : ℤ) * C.sy at hy
  change (C.point n).val 2 - 1 = C.seed.val 2 - 1 + (n : ℤ) * C.sz at hz
  have hsy : C.sy = 1 := exitAColumn_sy hm i hi
  have hsz : C.sz = 1 := exitAColumn_sz hm i hi
  rw [hsy, hsz, hc0, hc] at hx
  rw [hsy] at hy
  rw [hsz] at hz
  have hsx : C.seed.val 0 = octRadius m - 2 * (i : ℤ) + 1 :=
    exitAColumn_seed_coordinates hm i hi 0
  have hsy' : C.seed.val 1 = octRadius m + 2 * (i : ℤ) + 1 :=
    exitAColumn_seed_coordinates hm i hi 1
  have hsz' : C.seed.val 2 = 1 := exitAColumn_seed_coordinates hm i hi 2
  change (C.point n).val d = _
  fin_cases d
  · change (C.point n).val 0 = octRadius m - 2 * (i : ℤ) + 1 - (n % 2 : ℕ)
    omega
  · change (C.point n).val 1 = octRadius m + 2 * (i : ℤ) + 1 + n
    omega
  · change (C.point n).val 2 = 1 + n
    omega

private theorem exitAColumn_owner_deleted {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) :
    (exitAColumn hm i hi).owner ∈ bulkDeletedEdges m :=
  edgeZigzag_mem_deleted hm exitEdgeFrame (2 * i) (by omega)

private theorem column_points_ne_of_owner_ne {m : ℕ} (C D : DanglingColumn m)
    (howners : C.owner ≠ D.owner) (n r : ℕ) : C.point n ≠ D.point r := by
  intro heq
  exact howners (column_owner_eq_of_seed_eq C D (DanglingColumn.seeds_eq_of_point_eq C D heq))

private theorem deletedColumn_ne_bulkColumn {m : ℕ} (C D : DanglingColumn m)
    (hC : C.owner ∈ bulkDeletedEdges m) (hD : D.owner ∈ bulkInterior m) (n r : ℕ) :
    C.point n ≠ D.point r :=
  (bulkColumn_ne_edgeColumn D C hD hC r n).symm

private theorem exitAColumn_ne_bulkColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m)
    (D : DanglingColumn m) (hD : D.owner ∈ bulkInterior m) (n r : ℕ) :
    (exitAColumn hm i hi).point n ≠ D.point r :=
  deletedColumn_ne_bulkColumn (exitAColumn hm i hi) D
    (exitAColumn_owner_deleted hm i hi) hD n r

def exitCapColumn (p : ConstructionParameters) (k : ℕ) (_hk : k ≤ p.bins) : DanglingColumn p.side :=
  exitAColumn (by have h := p.side_ge; omega) (5 * p.exitSlot k + 5)
    (by have h := p.exit_column_triangle_room k; omega)

theorem exitCapColumn_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitCapColumn p k hk).owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10) := by
  change octEdgeZigzag p.side exitEdgeFrame (2 * (5 * p.exitSlot k + 5)) = _
  congr 1
  omega

theorem exitCapColumn_dir (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitCapColumn p k hk).dir = 0 := rfl

theorem exitCapColumn_owner_inA (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    InASublattice (exitCapColumn p k hk).owner.val :=
  (octEdgeZigzag_even (by have h := p.side_ge; omega : 1 ≤ p.side) exitEdgeFrame
    (5 * p.exitSlot k + 5)).1

theorem exitCapColumn_owner_colour (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    FarField.colour (exitCapColumn p k hk).owner = true := by
  have hA := exitCapColumn_owner_inA p k hk
  simp only [FarField.colour, hA, decide_true]

theorem exitCapColumn_owner_deleted (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitCapColumn p k hk).owner ∈ bulkDeletedEdges p.side :=
  exitAColumn_owner_deleted (by have h := p.side_ge; omega) (5 * p.exitSlot k + 5)
    (by have h := p.exit_column_triangle_room k; omega)

theorem exitCapColumn_point_coordinates (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (n : ℕ) (d : Fin 3) : ((exitCapColumn p k hk).point n).val d =
      if d = 0 then octRadius p.side - (10 * (p.exitSlot k : ℤ) + 10) + 1 - (n % 2 : ℕ)
      else if d = 1 then octRadius p.side + (10 * (p.exitSlot k : ℤ) + 10) + 1 + n else 1 + n := by
  dsimp only [exitCapColumn]
  rw [exitAColumn_point_coordinates]
  fin_cases d <;> dsimp <;> omega

theorem exitCapColumn_point_bounds (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) (n : ℕ) :
    4 ≤ ((exitCapColumn p k hk).point n).val 0 ∧
      1 ≤ bulkY p.side ((exitCapColumn p k hk).point n) ∧
      1 ≤ ((exitCapColumn p k hk).point n).val 2 := by
  have hx := exitCapColumn_point_coordinates p k hk n 0
  have hy := exitCapColumn_point_coordinates p k hk n 1
  have hz := exitCapColumn_point_coordinates p k hk n 2
  have hroom := p.exit_column_triangle_room k
  dsimp [octRadius] at hx hy hz ⊢
  change 4 ≤ _ ∧ 1 ≤ ((exitCapColumn p k hk).point n).val 1 - (2 * (p.side : ℤ) - 2) ∧ 1 ≤ _
  omega

theorem exitCapColumn_owner_injective (p : ConstructionParameters) {k l : ℕ}
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (heq : (exitCapColumn p k hk).owner = (exitCapColumn p l hl).owner) : k = l := by
  rw [exitCapColumn_owner, exitCapColumn_owner] at heq
  have h := octEdgeZigzag_injective (by have h := p.side_ge; omega : 1 ≤ p.side) exitEdgeFrame heq
  have hk' := p.exitSlot_add k hk
  have hl' := p.exitSlot_add l hl
  omega

theorem exitCapColumns_points_ne (p : ConstructionParameters) {k l : ℕ}
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l) (n r : ℕ) :
    (exitCapColumn p k hk).point n ≠ (exitCapColumn p l hl).point r := by
  exact column_points_ne_of_owner_ne (exitCapColumn p k hk) (exitCapColumn p l hl)
    (fun heq => hne (exitCapColumn_owner_injective p hk hl heq)) n r

theorem exitCapColumn_ne_BColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (D : DanglingColumn p.side) (hD : InBSublattice D.owner.val) (n r : ℕ) :
    (exitCapColumn p k hk).point n ≠ D.point r :=
  DanglingColumn.points_ne_of_owner_colours _ _ (exitCapColumn_owner_inA p k hk) hD n r

theorem exitCapColumn_ne_bulkColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (D : DanglingColumn p.side) (hD : D.owner ∈ bulkInterior p.side) (n r : ℕ) :
    (exitCapColumn p k hk).point n ≠ D.point r := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hi : 5 * p.exitSlot k + 5 < p.side := by
    have h := p.exit_column_triangle_room k
    omega
  dsimp only [exitCapColumn]
  with_reducible exact exitAColumn_ne_bulkColumn (m := p.side) hm (5 * p.exitSlot k + 5) hi D hD n r

theorem exitCapColumn_ne_trackAColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : ℕ) (hi : i < p.side) (n r : ℕ) :
    (exitCapColumn p k hk).point n ≠
      (trackAColumn (m := p.side) (by have h := p.side_ge; omega) i hi).point r := by
  intro heq
  have hc := (exitCapColumn_point_bounds p k hk n).2.1
  have hd := trackAColumn_negativeY (m := p.side) (by have h := p.side_ge; omega) i hi r
  rw [heq] at hc
  omega

theorem exitCapColumn_ne_frameEndpointColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (atStart : Bool) (n r : ℕ) :
    (exitCapColumn p k hk).point n ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point r := by
  intro heq
  have hc := (exitCapColumn_point_bounds p k hk n).2.1
  have hd := frameEndpointColumn_negativeY (m := p.side) (by have h := p.side_ge; omega) atStart r
  rw [heq] at hc
  omega

theorem exitCapColumn_ne_frameBorrowPoint (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius p.side)
    (mode : Bool) (n r : ℕ) : (exitCapColumn p k hk).point n ≠
      frameBorrowPoint (m := p.side) (by have h := p.side_ge; omega) i hi hilo hihi mode r := by
  intro heq
  have hc := (exitCapColumn_point_bounds p k hk n).1
  have hd := frameBorrowPoint_negativeX (m := p.side) (by have h := p.side_ge; omega) i hi hilo hihi mode r
  rw [heq] at hc
  omega

theorem exitCapColumn_ne_frameBorrowColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius p.side)
    (mode : Bool) (n r : ℕ) : (exitCapColumn p k hk).point n ≠
      (frameBorrowColumn (m := p.side) (by have h := p.side_ge; omega) i hi hilo hihi mode).point r := by
  intro heq
  have hc := (exitCapColumn_point_bounds p k hk n).1
  have hd := frameBorrowColumn_negativeX (m := p.side) (by have h := p.side_ge; omega) i hi hilo hihi mode r
  rw [heq] at hc
  omega

theorem exitCapColumn_ne_edgePPP (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (F : OctEdgeFrame) (r : ℕ) (hr : r + 2 < 2 * p.side - 1)
    (hp : (exitCapColumn p k hk).owner ≠ octEdgeZigzag p.side F r)
    (hq : (exitCapColumn p k hk).owner ≠ octEdgeZigzag p.side F (r + 2)) (n : ℕ) (s : Fin 3) :
    (exitCapColumn p k hk).point n ≠ (edgePPPFold p.side F r).pos s := by
  exact (edgePPPFold_ne_inner_edge_column p.side (by have h := p.side_ge; omega) F exitEdgeFrame
    r (10 * p.exitSlot k + 10) hr (by omega)
    (by have h := p.exit_column_triangle_room k; omega) (exitCapColumn p k hk)
    (exitCapColumn_owner p k hk) hp hq s n).symm

private theorem exitFrameOffset_top (r : Fin (nearFrameLength 4)) :
    nearFrameOffset 4 r.val 2 = 2 → r.val = 1 := by
  revert r
  decide

theorem exitAColumn_ne_frameP {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m)
    (hilo : 10 ≤ 2 * i) (hihi : (2 * i : ℤ) + 4 ≤ octRadius m)
    (hires : (2 * i) % 10 = 0) (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1)
    (hslot : kind = 4 → f % 10 = 5) (n : ℕ) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (exitAColumn hm i hi).point n ≠ nearFramePoint m f kind hf r := by
  intro heq
  have hx := congrArg (fun s : Site => s.val 0) heq
  have hz := congrArg (fun s : Site => s.val 2) heq
  change ((exitAColumn hm i hi).point n).val 0 = (nearFramePoint m f kind hf r).val 0 at hx
  change ((exitAColumn hm i hi).point n).val 2 = (nearFramePoint m f kind hf r).val 2 at hz
  have hcx := exitAColumn_point_coordinates hm i hi n 0
  have hcz := exitAColumn_point_coordinates hm i hi n 2
  dsimp at hcx hcz
  obtain ⟨hxl, hxu⟩ := nearFramePoint_coordinate_bounds m f kind hf r hr0 hrlast 0
  have hzu := (nearFramePoint_coordinate_bounds m f kind hf r hr0 hrlast 2).2
  rw [← heq, exitAColumn_point_coordinates] at hxl hxu hzu
  fin_cases kind
  all_goals dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh] at hxl hxu hzu
  · omega
  · omega
  · omega
  · omega
  · have hn : n = 0 := by omega
    have hz' : 1 + (n : ℤ) = -1 + nearFrameOffset 4 r.val 2 := by
      change ((exitAColumn hm i hi).point n).val 2 =
        nearFrameReference m f 4 2 + nearFrameOffset 4 r.val 2 at hz
      dsimp [nearFrameReference] at hz
      omega
    have hr1 : r.val = 1 := exitFrameOffset_top r (by omega)
    have hx' : octRadius m - 2 * (i : ℤ) + 1 = octRadius m - (f : ℤ) - 6 := by
      change ((exitAColumn hm i hi).point n).val 0 =
        nearFrameReference m f 4 0 + nearFrameOffset 4 r.val 0 at hx
      rw [hr1] at hx
      dsimp [nearFrameReference, nearFrameOffset, nearFrameOffsetTriple] at hx
      subst n
      dsimp at hcx
      omega
    have hres := hslot rfl
    omega
  · omega

theorem exitCapColumn_ne_frameLinkFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (j : FrameLinkIndex p) (n : ℕ) (r : Fin (nearFrameLength (frameLinkKind j) - 2)) :
    (exitCapColumn p k hk).point n ≠ (frameLinkFold p j).pos r := by
  apply exitAColumn_ne_frameP (m := p.side) (by have h := p.side_ge; omega)
    (5 * p.exitSlot k + 5) _ (by omega)
    (by have h := p.exit_column_triangle_room k; dsimp [octRadius]; omega)
    (by omega) (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_odd p j)
    (frameLink_exit_residue p j) n
    ⟨r.val + 1, by have h := r.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < _; have h := r.isLt; omega)

theorem faceColumn_nonpositiveZ (m a b c : ℕ) (hs : a + b + c + 2 = m) (n : ℕ) :
    ((faceDanglingColumn m a b c hs).point n).val 2 ≤ 0 := by
  have h := faceDanglingColumn_point_coordinates m a b c hs n 2
  dsimp at h
  omega

theorem borrowedPoint_nonpositiveZ (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (ha : 1 ≤ a) (n : ℕ) : (borrowedPoint m a b c hs ha n).val 2 ≤ 0 := by
  cases n with
  | zero => exact faceColumn_nonpositiveZ m a b c hs 0
  | succ n => exact faceColumn_nonpositiveZ m (a - 1) b (c + 1) (by omega) (n + 1)

theorem rowCBFold_nonpositiveZ (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b) (h₂ : l₂ ≤ a + l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    ((rowCBFold m j a b c l₁ l₂ hs h₁).pos i).val 2 ≤ 0 := by
  unfold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun s : Site => s.val 2 ≤ 0) ?_ ?_ i
  · intro r
    change -2 * (a : ℤ) - 1 - r.val ≤ 0
    omega
  · intro r
    have hr := r.isLt
    change -2 * ((a + l₁ : ℕ) : ℤ) - 1 + r.val ≤ 0
    omega

theorem rowBAFold_nonpositiveZ (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) :
    ((rowBAFold m j a b c l₁ l₂ hs h₁).pos i).val 2 ≤ 0 := by
  unfold rowBAFold
  apply glue_property _ _ _ _ _ _ (fun s : Site => s.val 2 ≤ 0) ?_ ?_ i
  · intro r
    have hr := r.isLt
    change -2 * (a : ℤ) - 1 + r.val ≤ 0
    omega
  · intro r
    change -2 * ((a - l₁ : ℕ) : ℤ) - 1 + (r.val % 2 : ℕ) ≤ 0
    omega

theorem entryTetherFold_nonpositiveZ (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) : ((entryTetherFold p k hk).pos i).val 2 ≤ 0 := by
  apply entryTetherFold_property p k hk (fun s : Site => s.val 2 ≤ 0) _ _ _ i
  · intro r
    exact borrowedPoint_nonpositiveZ p.side (entryAnchorA p k) (3 * (k + 1)) 0
      (entryAnchor_equation p k hk) (entryAnchor_positive p k hk) r.val
  · intro r
    unfold entryRowFold
    exact rowCBFold_nonpositiveZ _ _ _ _ _ _ _ _ _
      (by have h := p.separator_room k hk; have ht := p.entry_column_triangle_room k hk; omega) r
  · intro r
    exact faceColumn_nonpositiveZ p.side (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
      (by have h := p.separator_room k hk; omega) r.rev.val

theorem exitTetherFold_nonpositiveZ (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) : ((exitTetherFold p k hk).pos i).val 2 ≤ 0 := by
  apply exitTetherFold_property p k hk (fun s : Site => s.val 2 ≤ 0) _ _ _ i
  · intro r
    exact faceColumn_nonpositiveZ p.side (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
      (by have h := p.separator_room k hk; omega) r.val
  · intro r
    unfold exitRowFold
    exact rowBAFold_nonpositiveZ _ _ _ _ _ _ _ _ _ r
  · intro r
    exact faceColumn_nonpositiveZ p.side 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
      (by have h := p.exit_column_triangle_room k; omega) r.rev.val

theorem entryTetherFold_ne_exitCapColumn (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (p.entryTether k)) (n : ℕ) :
    (entryTetherFold p k hk).pos i ≠ (exitCapColumn p l hl).point n := by
  intro heq
  have h := entryTetherFold_nonpositiveZ p k hk i
  rw [heq] at h
  have h' := (exitCapColumn_point_bounds p l hl n).2.2
  omega

theorem exitTetherFold_ne_exitCapColumn (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (p.exitTether k)) (n : ℕ) :
    (exitTetherFold p k hk).pos i ≠ (exitCapColumn p l hl).point n := by
  intro heq
  have h := exitTetherFold_nonpositiveZ p k hk i
  rw [heq] at h
  have h' := (exitCapColumn_point_bounds p l hl n).2.2
  omega

end ProteinFolding.Tetrahedral.NearField
