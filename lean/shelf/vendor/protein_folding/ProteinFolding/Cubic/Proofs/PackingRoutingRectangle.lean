import ProteinFolding.Cubic.Proofs.CertificatesDirections
import Mathlib.Data.Fin.Rev

/-! Explicit rectangular exterior routes between distinct collinear ports.
The route descends, travels outwards, crosses between the port rows, returns,
and ascends. Different depths and distinct port rows give disjoint routes.
These constructions implement the completeness routing described in
`research/linear_routing_and_prefix.md`; they assert no complexity result. -/

namespace ProteinFolding.CubicPackingRouting

open CubicCertificates

def point (x y z : ℤ) : Site
  | 0 => x
  | 1 => y
  | 2 => z

/-- Number of edges, including the two vertical pillars. -/
def routeSteps (h r w : ℕ) : ℕ := 2 * h + 2 * r + w

/-- Five straight segments, with each shared corner assigned to the later
segment. The first port is `(d,u,0)` and the second is `(d,u+w,0)`. -/
def routePoint (d u : ℤ) (h r w k : ℕ) : Site :=
  if k < h then point d u (-(k : ℤ))
  else if k < h + r then point (d + k - h) u (-h)
  else if k < h + r + w then point (d + r) (u + k - h - r) (-h)
  else if k < h + 2 * r + w then point (d + 2 * r + h + w - k) (u + w) (-h)
  else point d (u + w) ((k : ℤ) - (2 * h + 2 * r + w))

def routePos (d u : ℤ) (h r w : ℕ) (i : Fin (routeSteps h r w + 1)) : Site :=
  routePoint d u h r w i.val

theorem routePos_injective (d u : ℤ) (h r w : ℕ)
    (_hh : 0 < h) (hr : 0 < r) (hw : 0 < w) :
    Function.Injective (routePos d u h r w) := by
  intro i j he
  change routePoint _ _ _ _ _ _ = routePoint _ _ _ _ _ _ at he
  unfold routePoint at he
  split_ifs at he <;>
    have hx := congrFun he 0 <;>
    have hy := congrFun he 1 <;>
    have hz := congrFun he 2 <;>
    dsimp only [point] at hx hy hz <;>
    apply Fin.ext <;> omega

theorem routePos_adjacent (d u : ℤ) (h r w : ℕ)
    (_hh : 0 < h) (hr : 0 < r) (hw : 0 < w)
    (i j : Fin (routeSteps h r w + 1)) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (routePos d u h r w i) (routePos d u h r w j) := by
  change latticeDistance (routePoint _ _ _ _ _ _) (routePoint _ _ _ _ _ _) = 1
  unfold routePoint
  split_ifs <;> try omega
  all_goals rw [distance_eq]; dsimp only [point]; omega

/-- A self-avoiding route with exactly `2h+2r+w` edges. -/
def rectangleRoute (d u : ℤ) (h r w : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w) :
    Fold cubicLattice (routeSteps h r w + 1) where
  pos := routePos d u h r w
  injective_pos := routePos_injective d u h r w hh hr hw
  consecutive := routePos_adjacent d u h r w hh hr hw

theorem routePos_first (d u : ℤ) (h r w : ℕ) (hh : 0 < h) :
    routePos d u h r w ⟨0, by unfold routeSteps; omega⟩ = point d u 0 := by
  simp [routePos, routePoint, hh]

theorem routePos_last (d u : ℤ) (h r w : ℕ) :
    routePos d u h r w ⟨routeSteps h r w, by omega⟩ = point d (u + w) 0 := by
  have h₁ : ¬routeSteps h r w < h := by unfold routeSteps; omega
  have h₂ : ¬routeSteps h r w < h + r := by unfold routeSteps; omega
  have h₃ : ¬routeSteps h r w < h + r + w := by unfold routeSteps; omega
  have h₄ : ¬routeSteps h r w < h + 2 * r + w := by unfold routeSteps; omega
  simp only [routePos, routePoint, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]
  congr 1
  unfold routeSteps
  omega

theorem routePos_first_P (d u : ℤ) (h r w : ℕ) (hh : 0 < h) :
    routePos d u h r w ⟨1, by unfold routeSteps; omega⟩ = point d u (-1) := by
  change routePoint d u h r w 1 = _
  unfold routePoint
  split_ifs <;> apply site_ext <;> dsimp only [point] <;> omega

theorem routePos_last_P (d u : ℤ) (h r w : ℕ) (hh : 0 < h) :
    routePos d u h r w ⟨routeSteps h r w - 1, by unfold routeSteps; omega⟩ =
      point d (u + w) (-1) := by
  have hs : routeSteps h r w = 2 * h + 2 * r + w := rfl
  change routePoint d u h r w (routeSteps h r w - 1) = _
  unfold routePoint
  split_ifs <;> apply site_ext <;> dsimp only [point] <;> omega

theorem routePos_bounds (d u : ℤ) (h r w : ℕ)
    (i : Fin (routeSteps h r w + 1)) :
    d ≤ routePos d u h r w i 0 ∧ routePos d u h r w i 0 ≤ d + r ∧
    u ≤ routePos d u h r w i 1 ∧ routePos d u h r w i 1 ≤ u + w ∧
    -(h : ℤ) ≤ routePos d u h r w i 2 ∧ routePos d u h r w i 2 ≤ 0 := by
  have hi := i.isLt
  unfold routeSteps at hi
  unfold routePos routePoint
  split_ifs <;> dsimp only [point] <;> omega

/-- A point is on one of the two vertical port pillars, or strictly outwards
of that line at the route's single horizontal depth. -/
theorem routePos_pillar_or_depth (d u : ℤ) (h r w : ℕ) (hr : 0 < r)
    (i : Fin (routeSteps h r w + 1)) :
    (routePos d u h r w i 0 = d ∧
      (routePos d u h r w i 1 = u ∨ routePos d u h r w i 1 = u + w)) ∨
    (d < routePos d u h r w i 0 ∧ routePos d u h r w i 2 = -(h : ℤ)) := by
  unfold routePos routePoint
  split_ifs <;> dsimp only [point] <;> omega

/-- All vertices except the two H terminals lie strictly outside the front
plane. In particular they cannot collide with any face H vertex. -/
theorem routePos_interior_negative (d u : ℤ) (h r w : ℕ) (hh : 0 < h)
    (i : Fin (routeSteps h r w + 1)) (hi : 0 < i.val)
    (hlast : i.val < routeSteps h r w) : routePos d u h r w i 2 < 0 := by
  unfold routeSteps at hlast
  unfold routePos routePoint
  split_ifs <;> dsimp only [point] <;> omega

/-- Distinct depth rectangles with four distinct port rows are disjoint,
regardless of either radius or the ordering of their intervals of rows. -/
theorem rectangleRoutes_disjoint (d u v : ℤ) (h h' r r' w w' : ℕ)
    (hr : 0 < r) (hr' : 0 < r') (hdepth : h ≠ h')
    (h₀₀ : u ≠ v) (h₀₁ : u ≠ v + w')
    (h₁₀ : u + w ≠ v) (h₁₁ : u + w ≠ v + w')
    (i : Fin (routeSteps h r w + 1)) (j : Fin (routeSteps h' r' w' + 1)) :
    routePos d u h r w i ≠ routePos d v h' r' w' j := by
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  obtain ⟨hi, hiu | hiu⟩ | ⟨hi, hiz⟩ := routePos_pillar_or_depth d u h r w hr i
  · obtain ⟨hj, hjv | hjv⟩ | ⟨hj, _⟩ := routePos_pillar_or_depth d v h' r' w' hr' j
    · exact h₀₀ (by omega)
    · exact h₀₁ (by omega)
    · omega
  · obtain ⟨hj, hjv | hjv⟩ | ⟨hj, _⟩ := routePos_pillar_or_depth d v h' r' w' hr' j
    · exact h₁₀ (by omega)
    · exact h₁₁ (by omega)
    · omega
  · obtain ⟨hj, _⟩ | ⟨_, hjz⟩ := routePos_pillar_or_depth d v h' r' w' hr' j
    · omega
    · omega

/-- Reverse the route when its desired first port is the upper row. -/
def reversedRectangleRoute (d u : ℤ) (h r w : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w) :
    Fold cubicLattice (routeSteps h r w + 1) where
  pos i := routePos d u h r w i.rev
  injective_pos := (routePos_injective d u h r w hh hr hw).comp Fin.rev_injective
  consecutive i j hij := by
    have hrev : j.rev.val + 1 = i.rev.val := by
      simp only [Fin.val_rev]
      omega
    exact (routePos_adjacent d u h r w hh hr hw j.rev i.rev hrev).symm

theorem reversedRectangleRoute_first (d u : ℤ) (h r w : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w) :
    (reversedRectangleRoute d u h r w hh hr hw).pos ⟨0, by omega⟩ = point d (u + w) 0 := by
  change routePos d u h r w (Fin.rev 0) = _
  rw [Fin.rev_zero]
  exact routePos_last d u h r w

theorem reversedRectangleRoute_last (d u : ℤ) (h r w : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w) :
    (reversedRectangleRoute d u h r w hh hr hw).pos
      ⟨routeSteps h r w, by omega⟩ = point d u 0 := by
  change routePos d u h r w (Fin.rev (Fin.last _)) = _
  rw [Fin.rev_last]
  exact routePos_first d u h r w hh

/-- Increasing the radius by one adds two edges. The parity condition and
the shortest-rectangle bound therefore suffice for every prescribed length. -/
theorem exists_radius_for_length (h w length : ℕ)
    (hbound : routeSteps h 1 w ≤ length) (hparity : length % 2 = w % 2) :
    ∃ r : ℕ, 0 < r ∧ routeSteps h r w = length := by
  refine ⟨1 + (length - routeSteps h 1 w) / 2, by omega, ?_⟩
  unfold routeSteps at *
  omega

/-- A long `P^(4n)` connector is exactly the rectangle after discarding the
two H terminals and the two exterior P sites already present in their words. -/
def connectorIndex (h r w n : ℕ) (hlen : routeSteps h r w = 4 * n + 3)
    (i : Fin (4 * n)) : Fin (routeSteps h r w + 1) := ⟨i.val + 2, by omega⟩

def rectangleConnector (d u : ℤ) (h r w n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w)
    (hlen : routeSteps h r w = 4 * n + 3) : Fold cubicLattice (4 * n) where
  pos i := routePos d u h r w (connectorIndex h r w n hlen i)
  injective_pos := by
    intro i j he
    have hv := congrArg Fin.val (routePos_injective d u h r w hh hr hw he)
    apply Fin.ext
    change i.val + 2 = j.val + 2 at hv
    omega
  consecutive i j hij := routePos_adjacent d u h r w hh hr hw _ _ (by
    change i.val + 2 + 1 = j.val + 2
    omega)

theorem rectangleConnector_negative (d u : ℤ) (h r w n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w)
    (hlen : routeSteps h r w = 4 * n + 3) (i : Fin (4 * n)) :
    (rectangleConnector d u h r w n hh hr hw hlen).pos i 2 < 0 := by
  exact routePos_interior_negative d u h r w hh _ (by change 0 < i.val + 2; omega)
    (by change i.val + 2 < routeSteps h r w; omega)

theorem rectangleConnector_below_face_P (d u : ℤ) (h r w n : ℕ)
    (hh : 2 ≤ h) (hr : 0 < r) (hw : 0 < w)
    (hlen : routeSteps h r w = 4 * n + 3) (i : Fin (4 * n)) :
    (rectangleConnector d u h r w n (by omega) hr hw hlen).pos i 2 ≤ -2 := by
  have hi := i.isLt
  unfold routeSteps at hlen
  change routePoint d u h r w (i.val + 2) 2 ≤ -2
  unfold routePoint
  split_ifs <;> dsimp only [point] <;> omega

theorem rectangleConnector_left_seam (d u : ℤ) (h r w n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w)
    (hlen : routeSteps h r w = 4 * n + 3) (i : Fin (4 * n)) (hi : i.val = 0) :
    cubicLattice.Adj
      (routePos d u h r w ⟨1, by omega⟩)
      ((rectangleConnector d u h r w n hh hr hw hlen).pos i) := by
  exact routePos_adjacent d u h r w hh hr hw _ _ (by
    change 1 + 1 = i.val + 2
    omega)

theorem rectangleConnector_right_seam (d u : ℤ) (h r w n : ℕ)
    (hh : 0 < h) (hr : 0 < r) (hw : 0 < w)
    (hlen : routeSteps h r w = 4 * n + 3) (i : Fin (4 * n)) (hi : i.val + 1 = 4 * n) :
    cubicLattice.Adj
      ((rectangleConnector d u h r w n hh hr hw hlen).pos i)
      (routePos d u h r w ⟨4 * n + 2, by omega⟩) := by
  exact routePos_adjacent d u h r w hh hr hw _ _ (by
    change i.val + 2 + 1 = 4 * n + 2
    omega)

end ProteinFolding.CubicPackingRouting
