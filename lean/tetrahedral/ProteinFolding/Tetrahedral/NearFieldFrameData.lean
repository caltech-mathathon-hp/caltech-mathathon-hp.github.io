import ProteinFolding.Tetrahedral.OctahedralTrackGeometry
import ProteinFolding.Tetrahedral.ColumnsSkins

/-! Literal Appendix C frame links. Kinds: initial Va, two-slot, incoming Vb,
outgoing Vb, six-slot, incoming Vc. Both endpoint H-sites are included. -/

namespace ProteinFolding.Tetrahedral

def nearFrameLength (kind : Fin 6) : ℕ :=
  if kind = 0 ∨ kind = 1 then 8 else if kind = 4 then 12 else 5

def nearFrameReferenceIsB (kind : Fin 6) : Prop := kind = 1 ∨ kind = 4
instance (kind : Fin 6) : Decidable (nearFrameReferenceIsB kind) := inferInstanceAs (Decidable (kind = 1 ∨ kind = 4))

def nearFrameIsA (kind : Fin 6) (i : ℕ) : Prop := if kind = 1 then i % 2 = 1 else i % 2 = 0
instance (kind : Fin 6) (i : ℕ) : Decidable (nearFrameIsA kind i) := by unfold nearFrameIsA; infer_instance

def nearFrameReference (m q : ℕ) (kind : Fin 6) (k : Fin 3) : ℤ :=
  if kind = 0 then
    if k = 0 then 0 else if k = 1 then octRadius m else -octRadius m
  else if kind = 1 then
    if k = 0 then 1 else if k = 1 then octRadius m + q else -octRadius m + q
  else if kind = 2 ∨ kind = 3 then
    if k = 0 then 0 else if k = 1 then 2 * octRadius m else 0
  else if kind = 4 then
    if k = 0 then octRadius m - q else if k = 1 then octRadius m + q else -1
  else if k = 0 then octRadius m else if k = 1 then octRadius m else 0

def nearFrameOffsetTriple (kind : Fin 6) (i : ℕ) : ℤ × ℤ × ℤ :=
  if kind = 0 then
    if i = 0 then (0,0,0) else if i = 1 then (-1,1,-1) else if i = 2 then (0,2,-2)
    else if i = 3 then (1,3,-1) else if i = 4 then (0,4,0) else if i = 5 then (1,5,1)
    else if i = 6 then (2,4,2) else (1,3,3)
  else if kind = 1 then
    if i = 0 then (0,0,0) else if i = 1 then (1,1,-1) else if i = 2 then (0,2,-2)
    else if i = 3 then (-1,3,-1) else if i = 4 then (0,4,0) else if i = 5 then (-1,5,1)
    else if i = 6 then (-2,4,2) else (-1,3,3)
  else if kind = 2 then
    if i = 0 then (0,-2,-2) else if i = 1 then (-1,-1,-3) else if i = 2 then (-2,0,-2)
    else if i = 3 then (-1,1,-1) else (0,0,0)
  else if kind = 3 then
    if i = 0 then (0,0,0) else if i = 1 then (1,1,1) else if i = 2 then (2,0,2)
    else if i = 3 then (3,-1,1) else (2,-2,0)
  else if kind = 4 then
    if i = 0 then (-7,7,1) else if i = 1 then (-6,8,2) else if i = 2 then (-5,9,1)
    else if i = 3 then (-4,8,0) else if i = 4 then (-3,7,1) else if i = 5 then (-2,6,0)
    else if i = 6 then (-1,5,1) else if i = 7 then (0,4,0) else if i = 8 then (1,3,1)
    else if i = 9 then (2,2,0) else if i = 10 then (1,1,-1) else (0,0,0)
  else if i = 0 then (-2,2,0) else if i = 1 then (-1,3,1) else if i = 2 then (0,2,2)
    else if i = 3 then (1,1,1) else (0,0,0)

def nearFrameOffset (kind : Fin 6) (i : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then (nearFrameOffsetTriple kind i).1
  else if k = 1 then (nearFrameOffsetTriple kind i).2.1 else (nearFrameOffsetTriple kind i).2.2

def nearFrameDirection (kind : Fin 6) (i : ℕ) : Fin 4 :=
  if kind = 0 then
    if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 1
    else if i = 4 then 0 else if i = 5 then 2 else 3
  else if kind = 1 then
    if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 0
    else if i = 4 then 1 else if i = 5 then 3 else 2
  else if kind = 2 then if i = 0 then 2 else if i = 1 then 1 else if i = 2 then 0 else 2
  else if kind = 4 then
    if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 2
    else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 1 else if i = 7 then 2
    else if i = 8 then 1 else if i = 9 then 0 else 3
  else if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else 0

def NearNegativeB (p : Coordinates) : Prop :=
  (∀ k, p k % 2 = 1) ∧ coordinateSum p % 4 = 1

instance (p : Coordinates) : Decidable (NearNegativeB p) := by unfold NearNegativeB; infer_instance

theorem nearFrameOffset_colour (kind : Fin 6) (i : Fin (nearFrameLength kind)) :
    if nearFrameReferenceIsB kind then
      (if nearFrameIsA kind i.val then NearNegativeB (nearFrameOffset kind i.val)
        else InASublattice (nearFrameOffset kind i.val))
    else (if nearFrameIsA kind i.val then InASublattice (nearFrameOffset kind i.val)
      else InBSublattice (nearFrameOffset kind i.val)) := by
  revert kind i
  decide

theorem nearFrameOffset_step (kind : Fin 6) (i : Fin (nearFrameLength kind - 1)) (k : Fin 3) :
    nearFrameOffset kind (i.val + 1) k = nearFrameOffset kind i.val k +
      if nearFrameIsA kind i.val then bondComponent (nearFrameDirection kind i.val) k
      else -bondComponent (nearFrameDirection kind i.val) k := by
  revert kind i k
  decide

theorem nearFrameOffset_injective (kind : Fin 6) :
    Function.Injective (fun i : Fin (nearFrameLength kind) => nearFrameOffset kind i.val) := by
  revert kind
  decide

theorem nearFrameReference_inA (m q : ℕ) (kind : Fin 6) (hk : ¬ nearFrameReferenceIsB kind) :
    InASublattice (nearFrameReference m q kind) := by
  change ¬ (kind = 1 ∨ kind = 4) at hk
  fin_cases kind
  all_goals first
    | exact (hk (Or.inl rfl)).elim
    | exact (hk (Or.inr rfl)).elim
    | (constructor
       · intro k
         fin_cases k <;> dsimp [nearFrameReference, octRadius] <;> omega
       · dsimp [coordinateSum, nearFrameReference, octRadius]; omega)

theorem nearFrameReference_inB (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hk : nearFrameReferenceIsB kind) : InBSublattice (nearFrameReference m q kind) := by
  change kind = 1 ∨ kind = 4 at hk
  rcases hk with rfl | rfl
  all_goals constructor
  all_goals first
    | (intro k; fin_cases k <;> dsimp [nearFrameReference, octRadius] <;> omega)
    | (dsimp [coordinateSum, nearFrameReference, octRadius]; omega)

theorem near_add_A_A {p q : Coordinates} (hp : InASublattice p) (hq : InASublattice q) :
    InASublattice (fun k => p k + q k) := by
  constructor
  · intro k; rw [Int.add_emod, hp.1 k, hq.1 k]; decide
  · rw [coordinateSum_add, Int.add_emod, hp.2, hq.2]; decide

theorem near_add_A_B {p q : Coordinates} (hp : InASublattice p) (hq : InBSublattice q) :
    InBSublattice (fun k => p k + q k) := by
  constructor
  · intro k; rw [Int.add_emod, hp.1 k, hq.1 k]; decide
  · rw [coordinateSum_add, Int.add_emod, hp.2, hq.2]; decide

theorem near_add_B_A {p q : Coordinates} (hp : InBSublattice p) (hq : InASublattice q) :
    InBSublattice (fun k => p k + q k) := by
  constructor
  · intro k; rw [Int.add_emod, hp.1 k, hq.1 k]; decide
  · rw [coordinateSum_add, Int.add_emod, hp.2, hq.2]; decide

theorem near_add_B_negativeB {p q : Coordinates} (hp : InBSublattice p) (hq : NearNegativeB q) :
    InASublattice (fun k => p k + q k) := by
  constructor
  · intro k; rw [Int.add_emod, hp.1 k, hq.1 k]; decide
  · rw [coordinateSum_add, Int.add_emod, hp.2, hq.2]; decide

def nearFrameCoordinates (m q : ℕ) (kind : Fin 6) (i : ℕ) : Coordinates :=
  fun k => nearFrameReference m q kind k + nearFrameOffset kind i k

theorem nearFrameCoordinates_colour (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind)) :
    if nearFrameIsA kind i.val then InASublattice (nearFrameCoordinates m q kind i.val)
    else InBSublattice (nearFrameCoordinates m q kind i.val) := by
  have hoff := nearFrameOffset_colour kind i
  by_cases href : nearFrameReferenceIsB kind
  · have hp := nearFrameReference_inB m q kind hq href
    rw [if_pos href] at hoff
    by_cases hi : nearFrameIsA kind i.val
    · rw [if_pos hi] at hoff ⊢
      exact near_add_B_negativeB hp hoff
    · rw [if_neg hi] at hoff ⊢
      exact near_add_B_A hp hoff
  · have hp := nearFrameReference_inA m q kind href
    rw [if_neg href] at hoff
    by_cases hi : nearFrameIsA kind i.val
    · rw [if_pos hi] at hoff ⊢
      exact near_add_A_A hp hoff
    · rw [if_neg hi] at hoff ⊢
      exact near_add_A_B hp hoff

def nearFramePoint (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (i : Fin (nearFrameLength kind)) : Site :=
  ⟨nearFrameCoordinates m q kind i.val, by
    have h := nearFrameCoordinates_colour m q kind hq i
    by_cases hi : nearFrameIsA kind i.val
    · exact Or.inl (by simpa only [if_pos hi] using h)
    · exact Or.inr (by simpa only [if_neg hi] using h)⟩

end ProteinFolding.Tetrahedral
