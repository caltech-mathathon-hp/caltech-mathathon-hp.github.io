import ProteinFolding.Tetrahedral.NearFieldFrameData

/-! Uniform halfspace bounds for every literal Appendix C offset. -/

namespace ProteinFolding.Tetrahedral

def nearFrameOffsetLow (kind : Fin 6) (i : Fin 4) : ℤ :=
  if kind = 0 then if i = 0 then -1 else if i = 1 then -5 else if i = 2 then -1 else -5
  else if kind = 1 then if i = 0 then 0 else if i = 1 then -8 else if i = 2 then 0 else -4
  else if kind = 2 then if i = 0 then -5 else if i = 1 then -1 else if i = 2 then 0 else -1
  else if kind = 3 then if i = 0 then 0 else if i = 1 then -1 else if i = 2 then -5 else -1
  else if kind = 4 then if i = 0 then 0 else if i = 1 then -16 else if i = 2 then 0 else -4
  else if i = 0 then 0 else if i = 1 then -5 else if i = 2 then -1 else -1

def nearFrameOffsetHigh (kind : Fin 6) (i : Fin 4) : ℤ :=
  if kind = 0 then if i = 0 then 8 else if i = 1 then 0 else if i = 2 then 4 else 0
  else if kind = 1 then if i = 0 then 5 else if i = 1 then 1 else if i = 2 then 5 else 1
  else if kind = 2 then if i = 0 then 0 else if i = 1 then 4 else if i = 2 then 4 else 0
  else if kind = 3 then if i = 0 then 4 else if i = 1 then 4 else if i = 2 then 0 else 0
  else if kind = 4 then if i = 0 then 5 else if i = 1 then 1 else if i = 2 then 13 else 1
  else if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 4 else 0

theorem nearFrameOffset_bounds (kind : Fin 6) (r : Fin (nearFrameLength kind)) (i : Fin 4) :
    nearFrameOffsetLow kind i ≤ tetraCoordinate 1 (nearFrameOffset kind r.val) i ∧
      tetraCoordinate 1 (nearFrameOffset kind r.val) i ≤ nearFrameOffsetHigh kind i := by
  revert kind r i
  decide

theorem tetraCoordinate_add_linear (m : ℕ) (p q : Coordinates) (i : Fin 4) :
    tetraCoordinate m (fun k => p k + q k) i = tetraCoordinate m p i + tetraCoordinate 1 q i := by
  fin_cases i <;> dsimp [tetraCoordinate, octRadius] <;> omega

theorem nearFramePoint_mem_solid_one (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) (r : Fin (nearFrameLength kind)) :
    nearFramePoint m q kind hq r ∈ skinSolid m 1 := by
  rw [mem_skinSolid]
  intro i
  have hb := nearFrameOffset_bounds kind r i
  change -(2 * ((m + 2 * 1 : ℕ) : ℤ) - 1) ≤
      tetraCoordinate m (fun k => nearFrameReference m q kind k + nearFrameOffset kind r.val k) i ∧
    tetraCoordinate m (fun k => nearFrameReference m q kind k + nearFrameOffset kind r.val k) i ≤
      2 * ((m + 2 * 1 : ℕ) : ℤ) - 2
  simp only [tetraCoordinate_add_linear]
  fin_cases kind <;> fin_cases i <;>
    dsimp [nearFrameReference, nearFrameOffsetLow, nearFrameOffsetHigh, tetraCoordinate, octRadius] at hb hqhi ⊢
  all_goals constructor <;> omega

def nearFrameOutsideFace (kind : Fin 6) (r : ℕ) : Fin 4 :=
  if kind = 0 then if r = 6 then 3 else 2
  else if kind = 1 then if r = 1 then 3 else 2
  else if kind = 2 then 2 else if kind = 4 then if r = 10 then 3 else 0 else 0

def nearFrameOutsideUpper (kind : Fin 6) (r : ℕ) : Prop := nearFrameOutsideFace kind r ≠ 3
instance (kind : Fin 6) (r : ℕ) : Decidable (nearFrameOutsideUpper kind r) := by
  unfold nearFrameOutsideUpper; infer_instance

theorem nearFrameOffset_exterior (kind : Fin 6) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    if nearFrameOutsideUpper kind r.val then
      2 ≤ tetraCoordinate 1 (nearFrameOffset kind r.val) (nearFrameOutsideFace kind r.val)
    else tetraCoordinate 1 (nearFrameOffset kind r.val) (nearFrameOutsideFace kind r.val) ≤ -2 := by
  revert kind r hr0 hrlast
  decide

theorem nearFrameOutside_reference (m q : ℕ) (kind : Fin 6) (r : ℕ) :
    if nearFrameOutsideUpper kind r then
      octRadius m - 1 ≤ tetraCoordinate m (nearFrameReference m q kind) (nearFrameOutsideFace kind r)
    else tetraCoordinate m (nearFrameReference m q kind) (nearFrameOutsideFace kind r) ≤ -octRadius m := by
  fin_cases kind <;> dsimp [nearFrameOutsideUpper, nearFrameOutsideFace]
  all_goals try split_ifs
  all_goals dsimp [nearFrameReference, tetraCoordinate, octRadius]
  all_goals omega

theorem nearFramePoint_outside (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    nearFramePoint m q kind hq r ∉ octahedron m := by
  intro hp
  have hb := (mem_octahedron m _).mp hp (nearFrameOutsideFace kind r.val)
  have ho := nearFrameOffset_exterior kind r hr0 hrlast
  have href := nearFrameOutside_reference m q kind r.val
  have heq := tetraCoordinate_add_linear m (nearFrameReference m q kind) (nearFrameOffset kind r.val)
    (nearFrameOutsideFace kind r.val)
  change tetraCoordinate m (nearFramePoint m q kind hq r).val (nearFrameOutsideFace kind r.val) = _ at heq
  by_cases hupper : nearFrameOutsideUpper kind r.val
  · rw [if_pos hupper] at ho href
    omega
  · rw [if_neg hupper] at ho href
    dsimp [octRadius] at href
    omega

theorem nearFramePoint_mem_skin_one (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    nearFramePoint m q kind hq r ∈ skin m 1 := by
  apply Finset.mem_sdiff.mpr
  refine ⟨nearFramePoint_mem_solid_one m q kind hq hqlo hqhi r, ?_⟩
  simpa only [Nat.sub_self, skinSolid_zero] using nearFramePoint_outside m q kind hq r hr0 hrlast

end ProteinFolding.Tetrahedral
