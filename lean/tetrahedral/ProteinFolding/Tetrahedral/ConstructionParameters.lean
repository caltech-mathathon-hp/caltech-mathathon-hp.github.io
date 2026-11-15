import ProteinFolding.Tetrahedral.RootSum

/-! The exact scale, track and tether parameters from Section 6.
Separator indices in this file are zero based: k=0,...,K corresponds to
the manuscript's separator k+1. -/

namespace ProteinFolding.Tetrahedral

structure ConstructionParameters where
  bins : ℕ
  capacity : ℕ
  bins_pos : 0 < bins
  capacity_pos : 0 < capacity

namespace ConstructionParameters

def sigma (p : ConstructionParameters) : ℕ := 18 * p.bins + 40
def scale (p : ConstructionParameters) : ℕ := p.sigma + 8
def binDimers (p : ConstructionParameters) : ℕ := p.scale * p.capacity
def leftFiller (p : ConstructionParameters) : ℕ := p.binDimers + p.scale
def rightFiller (p : ConstructionParameters) : ℕ := p.leftFiller + 1
def separatorIndex (p : ConstructionParameters) (k : ℕ) : ℕ :=
  p.leftFiller + k * (p.binDimers + 2)
def side (p : ConstructionParameters) : ℕ := p.separatorIndex p.bins + p.rightFiller + 3
def itemDimers (p : ConstructionParameters) (s : ℕ) : ℕ := p.scale * s
def entrySlack (_p : ConstructionParameters) (k : ℕ) : ℕ := 10 * k + 12
def exitSlack (p : ConstructionParameters) (k : ℕ) : ℕ := 14 * p.bins + 16 - 6 * k
def baseLinkerLength (p : ConstructionParameters) (w : ℕ) : ℕ :=
  1000 * (p.side + w + 1) + 6
def longLinkerLength (p : ConstructionParameters) (w : ℕ) (sameSublattice : Bool) : ℕ :=
  p.baseLinkerLength w + if sameSublattice then 1 else 0

theorem scale_eq (p : ConstructionParameters) : p.scale = 18 * p.bins + 48 := by
  simp [scale, sigma]

theorem scale_even (p : ConstructionParameters) : p.scale % 2 = 0 := by
  rw [scale_eq]
  omega

theorem binDimers_even (p : ConstructionParameters) : p.binDimers % 2 = 0 := by
  simp [binDimers, Nat.mul_mod, scale_even]

theorem leftFiller_even (p : ConstructionParameters) : p.leftFiller % 2 = 0 := by
  simp [leftFiller, Nat.add_mod, binDimers_even, scale_even]

theorem rightFiller_odd (p : ConstructionParameters) : p.rightFiller % 2 = 1 := by
  simp [rightFiller, Nat.add_mod, leftFiller_even]

theorem separatorIndex_even (p : ConstructionParameters) (k : ℕ) :
    p.separatorIndex k % 2 = 0 := by
  simp [separatorIndex, Nat.add_mod, Nat.mul_mod, binDimers_even, leftFiller_even]

theorem side_eq_track (p : ConstructionParameters) :
    p.side = 2 * p.leftFiller + p.bins * (p.binDimers + 2) + 4 := by
  simp only [side, separatorIndex, rightFiller]
  ring

theorem side_even (p : ConstructionParameters) : p.side % 2 = 0 := by
  simp [side, Nat.add_mod, separatorIndex_even, rightFiller_odd]

/-- The polynomial size formula used to bound the reduction. -/
theorem side_closedForm (p : ConstructionParameters) :
    p.side = (p.bins + 2) * (18 * p.bins + 48) * p.capacity + 38 * p.bins + 100 := by
  simp only [side, separatorIndex, rightFiller, leftFiller, binDimers, scale, sigma]
  ring

theorem scale_ge (p : ConstructionParameters) : 66 ≤ p.scale := by
  have h := p.bins_pos
  rw [scale_eq]
  omega

theorem binDimers_ge_scale (p : ConstructionParameters) : p.scale ≤ p.binDimers := by
  have h := Nat.mul_le_mul_left p.scale (show 1 ≤ p.capacity by have h := p.capacity_pos; omega)
  simpa [binDimers] using h

theorem binDimers_ge (p : ConstructionParameters) : 66 ≤ p.binDimers :=
  p.scale_ge.trans p.binDimers_ge_scale

theorem leftFiller_ge (p : ConstructionParameters) : 132 ≤ p.leftFiller := by
  have hs := p.scale_ge
  have hc := p.binDimers_ge
  unfold leftFiller
  omega

theorem rightFiller_ge (p : ConstructionParameters) : 133 ≤ p.rightFiller := by
  have h := p.leftFiller_ge
  unfold rightFiller
  omega

theorem side_ge (p : ConstructionParameters) : 336 ≤ p.side := by
  have hJ := p.leftFiller_ge
  have hC := p.binDimers_ge
  have hK := p.bins_pos
  have hmul := Nat.mul_le_mul_right (p.binDimers + 2) (show 1 ≤ p.bins by omega)
  simp only [Nat.one_mul] at hmul
  rw [side_eq_track]
  omega

theorem family_side_bound (p : ConstructionParameters) : 5 * p.bins + 40 ≤ p.side := by
  have hJ := p.leftFiller_ge
  have hC := p.binDimers_ge
  have hmul := Nat.mul_le_mul_left p.bins (show 68 ≤ p.binDimers + 2 by omega)
  rw [side_eq_track]
  omega

theorem separatorIndex_mono (p : ConstructionParameters) : Monotone p.separatorIndex := by
  intro k l hkl
  have hmul := Nat.mul_le_mul_right (p.binDimers + 2) hkl
  unfold separatorIndex
  omega

theorem separator_spacing (p : ConstructionParameters) (k : ℕ) :
    p.separatorIndex (k + 1) - p.separatorIndex k = p.binDimers + 2 := by
  simp only [separatorIndex, Nat.add_mul, Nat.one_mul]
  omega

theorem separator_room (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    p.separatorIndex k + p.rightFiller + 3 ≤ p.side := by
  have h := p.separatorIndex_mono hk
  unfold side
  omega

theorem entrySlack_even (p : ConstructionParameters) (k : ℕ) : p.entrySlack k % 2 = 0 := by
  simp only [entrySlack]
  omega

theorem exitSlack_even (p : ConstructionParameters) (k : ℕ) : p.exitSlack k % 2 = 0 := by
  simp only [exitSlack]
  omega

theorem tether_slack_bounds (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    p.entrySlack k ≤ 14 * p.bins + 16 ∧ p.exitSlack k ≤ 14 * p.bins + 16 ∧
      14 * p.bins + 16 < p.sigma ∧ 0 < p.exitSlack k := by
  simp only [entrySlack, exitSlack, sigma]
  omega

theorem itemDimers_even (p : ConstructionParameters) (s : ℕ) : p.itemDimers s % 2 = 0 := by
  simp [itemDimers, Nat.mul_mod, scale_even]

theorem itemDimers_ge (p : ConstructionParameters) (s : ℕ) (hs : 0 < s) :
    66 ≤ p.itemDimers s := by
  have hmul := Nat.mul_le_mul_left p.scale (show 1 ≤ s by omega)
  have h := p.scale_ge
  unfold itemDimers
  omega

theorem itemDimers_sum (p : ConstructionParameters) (items : List ℕ) :
    (items.map p.itemDimers).sum = p.scale * items.sum := by
  induction items with
  | nil => simp
  | cons s items ih => simp [itemDimers, ih, Nat.mul_add]

theorem scaled_total (p : ConstructionParameters) (items : List ℕ)
    (h : items.sum = p.bins * p.capacity) :
    (items.map p.itemDimers).sum = p.bins * p.binDimers := by
  rw [itemDimers_sum, h]
  unfold binDimers
  ring

theorem baseLinkerLength_even (p : ConstructionParameters) (w : ℕ) :
    p.baseLinkerLength w % 2 = 0 := by
  unfold baseLinkerLength
  omega

theorem longLinkerLength_parity (p : ConstructionParameters) (w : ℕ) (b : Bool) :
    p.longLinkerLength w b % 2 = if b then 1 else 0 := by
  cases b <;> simp [longLinkerLength, Nat.add_mod, baseLinkerLength_even]

end ConstructionParameters

end ProteinFolding.Tetrahedral
