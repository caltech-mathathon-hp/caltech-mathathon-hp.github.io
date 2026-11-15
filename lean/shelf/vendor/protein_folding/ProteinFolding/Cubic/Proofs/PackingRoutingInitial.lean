import ProteinFolding.Cubic.Proofs.PackingRoutingRectangle

/-! The exceptional first item connection. The final J terminal has x=d+1.
At depth four it moves to the unused row zero, then joins an ordinary
rectangular route at depth at least five. No item port uses row zero. -/

namespace ProteinFolding.CubicPackingRouting

open CubicCertificates

def initialSteps (h r Y v : ℕ) : ℕ := routeSteps h r v + Y + 1

def initialPoint (d : ℤ) (h r Y v k : ℕ) : Site :=
  if k < 4 then point (d + 1) Y (-(k : ℤ))
  else if k < Y + 5 then point (d + 1) ((Y : ℤ) + 4 - k) (-4)
  else routePoint d 0 h r v (k - Y - 1)

def initialPos (d : ℤ) (h r Y v : ℕ) (i : Fin (initialSteps h r Y v + 1)) : Site :=
  initialPoint d h r Y v i.val

def initialTailIndex (h r Y v : ℕ) (i : Fin (initialSteps h r Y v + 1))
    (_hi : Y + 5 ≤ i.val) : Fin (routeSteps h r v + 1) :=
  ⟨i.val - Y - 1, by have hi := i.isLt; unfold initialSteps at hi; omega⟩

theorem initialPos_tail (d : ℤ) (h r Y v : ℕ)
    (i : Fin (initialSteps h r Y v + 1)) (hi : Y + 5 ≤ i.val) :
    initialPos d h r Y v i = routePos d 0 h r v (initialTailIndex h r Y v i hi) := by
  have h₁ : ¬i.val < 4 := by omega
  have h₂ : ¬i.val < Y + 5 := by omega
  simp only [initialPos, initialPoint, if_neg h₁, if_neg h₂]
  rfl

theorem initialPos_prefix (d : ℤ) (h r Y v : ℕ)
    (i : Fin (initialSteps h r Y v + 1)) (hi : i.val < Y + 5) :
    initialPos d h r Y v i =
      if i.val < 4 then point (d + 1) Y (-(i.val : ℤ))
      else point (d + 1) ((Y : ℤ) + 4 - i.val) (-4) := by
  by_cases h₁ : i.val < 4 <;> simp only [initialPos, initialPoint, hi, h₁, ↓reduceIte]

theorem initialPos_prefix_location (d : ℤ) (h r Y v : ℕ)
    (i : Fin (initialSteps h r Y v + 1)) (hi : i.val < Y + 5) :
    initialPos d h r Y v i 0 = d + 1 ∧ -4 ≤ initialPos d h r Y v i 2 := by
  rw [initialPos_prefix d h r Y v i hi]
  split_ifs <;> dsimp only [point] <;> omega

theorem shallow_outer_ne_route (d : ℤ) (h r v : ℕ) (hh : 5 ≤ h) (hr : 0 < r)
    (p : Site) (hx : p 0 = d + 1) (hz : -4 ≤ p 2)
    (j : Fin (routeSteps h r v + 1)) : p ≠ routePos d 0 h r v j := by
  intro he
  have hxe := congrFun he 0
  have hze := congrFun he 2
  obtain ⟨hj, _⟩ | ⟨_, hj⟩ := routePos_pillar_or_depth d 0 h r v hr j
  · omega
  · omega

theorem initialPos_injective (d : ℤ) (h r Y v : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v) : Function.Injective (initialPos d h r Y v) := by
  intro i j he
  by_cases hi : i.val < Y + 5
  · by_cases hj : j.val < Y + 5
    · rw [initialPos_prefix d h r Y v i hi, initialPos_prefix d h r Y v j hj] at he
      split_ifs at he <;>
        have hy := congrFun he 1 <;>
        have hz := congrFun he 2 <;>
        dsimp only [point] at hy hz <;>
        apply Fin.ext <;> omega
    · obtain ⟨hx, hz⟩ := initialPos_prefix_location d h r Y v i hi
      rw [initialPos_tail d h r Y v j (by omega)] at he
      exact False.elim (shallow_outer_ne_route d h r v hh hr _ hx hz _ he)
  · by_cases hj : j.val < Y + 5
    · obtain ⟨hx, hz⟩ := initialPos_prefix_location d h r Y v j hj
      rw [initialPos_tail d h r Y v i (by omega)] at he
      exact False.elim (shallow_outer_ne_route d h r v hh hr _ hx hz _ he.symm)
    · rw [initialPos_tail d h r Y v i (by omega), initialPos_tail d h r Y v j (by omega)] at he
      have hv := congrArg Fin.val (routePos_injective d 0 h r v (by omega) hr hv he)
      apply Fin.ext
      change i.val - Y - 1 = j.val - Y - 1 at hv
      omega

theorem initialPos_adjacent (d : ℤ) (h r Y v : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (i j : Fin (initialSteps h r Y v + 1)) (hij : i.val + 1 = j.val) :
    cubicLattice.Adj (initialPos d h r Y v i) (initialPos d h r Y v j) := by
  by_cases hi : i.val < Y + 5
  · by_cases hj : j.val < Y + 5
    · rw [initialPos_prefix d h r Y v i hi, initialPos_prefix d h r Y v j hj]
      change latticeDistance _ _ = 1
      split_ifs <;> try omega
      all_goals rw [distance_eq]; dsimp only [point]; omega
    · have hiv : i.val = Y + 4 := by omega
      have hjv : j.val = Y + 5 := by omega
      have hfirst : ¬i.val < 4 := by omega
      rw [initialPos_prefix d h r Y v i hi, if_neg hfirst,
        initialPos_tail d h r Y v j (by omega)]
      have hk : (initialTailIndex h r Y v j (by omega)).val = 4 := by
        change j.val - Y - 1 = 4
        omega
      change latticeDistance _ (routePoint _ _ _ _ _ _) = 1
      rw [hk]
      have h4 : 4 < h := by omega
      simp only [routePoint, if_pos h4]
      rw [distance_eq]
      dsimp only [point]
      omega
  · have hj : Y + 5 ≤ j.val := by omega
    rw [initialPos_tail d h r Y v i (by omega), initialPos_tail d h r Y v j hj]
    exact routePos_adjacent d 0 h r v (by omega) hr hv _ _ (by
      change i.val - Y - 1 + 1 = j.val - Y - 1
      omega)

def initialRoute (d : ℤ) (h r Y v : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v) :
    Fold cubicLattice (initialSteps h r Y v + 1) where
  pos := initialPos d h r Y v
  injective_pos := initialPos_injective d h r Y v hh hr hv
  consecutive := initialPos_adjacent d h r Y v hh hr hv

theorem initialPos_first (d : ℤ) (h r Y v : ℕ) :
    initialPos d h r Y v ⟨0, by unfold initialSteps; omega⟩ = point (d + 1) Y 0 := rfl

theorem initialPos_first_P (d : ℤ) (h r Y v : ℕ) (hh : 5 ≤ h) :
    initialPos d h r Y v ⟨1, by unfold initialSteps routeSteps; omega⟩ =
      point (d + 1) Y (-1) := rfl

theorem initialPos_last (d : ℤ) (h r Y v : ℕ) (hh : 5 ≤ h) :
    initialPos d h r Y v ⟨initialSteps h r Y v, by omega⟩ = point d v 0 := by
  have h₁ : ¬initialSteps h r Y v < 4 := by unfold initialSteps routeSteps; omega
  have h₂ : ¬initialSteps h r Y v < Y + 5 := by unfold initialSteps routeSteps; omega
  have hk : initialSteps h r Y v - Y - 1 = routeSteps h r v := by unfold initialSteps; omega
  change initialPoint d h r Y v (initialSteps h r Y v) = _
  simp only [initialPoint, if_neg h₁, if_neg h₂, hk]
  exact (routePos_last d 0 h r v).trans (by simp)

theorem initialPos_special_or_route (d : ℤ) (h r Y v : ℕ)
    (i : Fin (initialSteps h r Y v + 1)) :
    (initialPos d h r Y v i 0 = d + 1 ∧ -4 ≤ initialPos d h r Y v i 2) ∨
    ∃ j : Fin (routeSteps h r v + 1), 4 ≤ j.val ∧
      initialPos d h r Y v i = routePos d 0 h r v j := by
  by_cases hi : i.val < Y + 5
  · exact Or.inl (initialPos_prefix_location d h r Y v i hi)
  · refine Or.inr ⟨initialTailIndex h r Y v i (by omega), ?_, initialPos_tail _ _ _ _ _ i (by omega)⟩
    change 4 ≤ i.val - Y - 1
    omega

/-- The depth-four transfer and the initial route avoid every later
rectangle with distinct port rows and its own depth at least five. -/
theorem initialRoute_disjoint_rectangle (d u : ℤ) (h h' r r' Y v w : ℕ)
    (hr : 0 < r) (hr' : 0 < r') (hdeep : 5 ≤ h') (hdepth : h ≠ h')
    (h₀₀ : (0 : ℤ) ≠ u) (h₀₁ : (0 : ℤ) ≠ u + w)
    (h₁₀ : (v : ℤ) ≠ u) (h₁₁ : (v : ℤ) ≠ u + w)
    (i : Fin (initialSteps h r Y v + 1)) (j : Fin (routeSteps h' r' w + 1)) :
    initialPos d h r Y v i ≠ routePos d u h' r' w j := by
  intro he
  obtain ⟨hx, hz⟩ | ⟨k, _, hk⟩ := initialPos_special_or_route d h r Y v i
  · have hxe := congrFun he 0
    have hze := congrFun he 2
    obtain ⟨hj, _⟩ | ⟨_, hj⟩ := routePos_pillar_or_depth d u h' r' w hr' j
    · omega
    · omega
  · exact rectangleRoutes_disjoint d 0 u h h' r r' v w hr hr' hdepth
      h₀₀ h₀₁ (by simpa using h₁₀) (by simpa using h₁₁) k j (hk.symm.trans he)

theorem exists_initial_radius_for_length (h Y v length : ℕ)
    (hbound : initialSteps h 1 Y v ≤ length)
    (hparity : length % 2 = (Y + v + 1) % 2) :
    ∃ r : ℕ, 0 < r ∧ initialSteps h r Y v = length := by
  refine ⟨1 + (length - initialSteps h 1 Y v) / 2, by omega, ?_⟩
  unfold initialSteps routeSteps at *
  omega

theorem exists_initial_frame_radius (d Y v : ℕ) (hd : 0 < d)
    (hY : Y ≤ d) (hv : v ≤ d) (hYe : Y % 2 = 0) (hve : v % 2 = 0) :
    ∃ r : ℕ, 0 < r ∧ initialSteps 5 r Y v = 4 * (d + 2) + 3 := by
  apply exists_initial_radius_for_length
  · unfold initialSteps routeSteps
    omega
  · omega

def initialConnectorIndex (h r Y v n : ℕ) (hlen : initialSteps h r Y v = 4 * n + 3)
    (i : Fin (4 * n)) : Fin (initialSteps h r Y v + 1) := ⟨i.val + 2, by omega⟩

/-- Exactly the inserted `4n` P residues of the first item connection. -/
def initialConnector (d : ℤ) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) : Fold cubicLattice (4 * n) where
  pos i := initialPos d h r Y v (initialConnectorIndex h r Y v n hlen i)
  injective_pos := by
    intro i j he
    have he' := congrArg Fin.val (initialPos_injective d h r Y v hh hr hv he)
    apply Fin.ext
    change i.val + 2 = j.val + 2 at he'
    omega
  consecutive i j hij := initialPos_adjacent d h r Y v hh hr hv _ _ (by
    change i.val + 2 + 1 = j.val + 2
    omega)

theorem initialConnector_below_face_P (d : ℤ) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) (i : Fin (4 * n)) :
    (initialConnector d h r Y v n hh hr hv hlen).pos i 2 ≤ -2 := by
  have hi := i.isLt
  unfold initialSteps routeSteps at hlen
  change initialPoint d h r Y v (i.val + 2) 2 ≤ -2
  unfold initialPoint routePoint
  split_ifs <;> dsimp only [point] <;> omega

theorem initialConnector_left_seam (d : ℤ) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) (i : Fin (4 * n)) (hi : i.val = 0) :
    cubicLattice.Adj (point (d + 1) Y (-1))
      ((initialConnector d h r Y v n hh hr hv hlen).pos i) := by
  rw [← initialPos_first_P d h r Y v hh]
  exact initialPos_adjacent d h r Y v hh hr hv _ _ (by
    change 1 + 1 = i.val + 2
    omega)

theorem initialPos_last_P (d : ℤ) (h r Y v : ℕ) (hh : 5 ≤ h) :
    initialPos d h r Y v ⟨initialSteps h r Y v - 1, by unfold initialSteps routeSteps; omega⟩ =
      point d v (-1) := by
  have hs : initialSteps h r Y v = routeSteps h r v + Y + 1 := rfl
  have hi : Y + 5 ≤ initialSteps h r Y v - 1 := by
    unfold routeSteps at hs
    omega
  rw [initialPos_tail d h r Y v _ hi]
  have hind : initialTailIndex h r Y v ⟨initialSteps h r Y v - 1, by
      unfold initialSteps routeSteps; omega⟩ hi =
      ⟨routeSteps h r v - 1, by unfold routeSteps; omega⟩ := by
    apply Fin.ext
    change initialSteps h r Y v - 1 - Y - 1 = routeSteps h r v - 1
    omega
  rw [hind, routePos_last_P d 0 h r v (by omega)]
  simp

theorem initialConnector_right_seam (d : ℤ) (h r Y v n : ℕ)
    (hh : 5 ≤ h) (hr : 0 < r) (hv : 0 < v)
    (hlen : initialSteps h r Y v = 4 * n + 3) (i : Fin (4 * n)) (hi : i.val + 1 = 4 * n) :
    cubicLattice.Adj ((initialConnector d h r Y v n hh hr hv hlen).pos i)
      (point d v (-1)) := by
  rw [← initialPos_last_P d h r Y v hh]
  exact initialPos_adjacent d h r Y v hh hr hv _ _ (by
    change i.val + 2 + 1 = initialSteps h r Y v - 1
    omega)

end ProteinFolding.CubicPackingRouting
