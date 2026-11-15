import ProteinFolding.Tetrahedral.FarFieldPaddingArithmetic

/-! The actual two-avenue detour of Lemma F(D), including the optional
four-site detour. The path is represented by an injective finite position
function, using exactly the same `Fold` path semantics as the HP problem. -/

namespace ProteinFolding.Tetrahedral.FarField

set_option maxHeartbeats 1600000

def segmentOne (r : ℕ) (δ : Bool) (d : ℕ) : ℕ := r + 4 * d + 1 - δ.toNat
def segmentTwo (d : ℕ) : ℕ := 4 * d + 5
def segmentThree (b : ℕ) (δ η : Bool) : ℕ := if η then 5 - δ.toNat else b - δ.toNat - 3
def segmentFour (η : Bool) : ℕ := if η then 4 else 0
def segmentFive (b : ℕ) (η : Bool) : ℕ := if η then b - 8 else 0

def routeLength (r b : ℕ) (δ η : Bool) (d : ℕ) : ℕ :=
  segmentOne r δ d + segmentTwo d + segmentThree b δ η + segmentFour η + segmentFive b η

def routeIndex (r b : ℕ) (δ η : Bool) (d i : ℕ) : Bool × ℤ :=
  let n₁ := segmentOne r δ d
  let n₂ := segmentTwo d
  let n₃ := segmentThree b δ η
  let n₄ := segmentFour η
  if i < n₁ then (false, (r : ℤ) - i)
  else if i < n₁ + n₂ then
    (true, lowCrossing δ d - crossingSign δ + (i - n₁ : ℕ))
  else if i < n₁ + n₂ + n₃ then
    (false, highCrossing δ + (i - (n₁ + n₂) : ℕ))
  else if i < n₁ + n₂ + n₃ + n₄ then
    (true, 7 + (i - (n₁ + n₂ + n₃) : ℕ))
  else (false, 9 + (i - (n₁ + n₂ + n₃ + n₄) : ℕ))

theorem routeLength_positive (r b : ℕ) (δ η : Bool) (d : ℕ) :
    0 < routeLength r b δ η d := by
  unfold routeLength segmentTwo
  omega

theorem routeLength_exact (r b : ℕ) (δ η : Bool) (d : ℕ)
    (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b) :
    (routeLength r b δ η d : ℤ) = (b : ℤ) - r + 1 + paddingIncrease r δ η d := by
  cases δ <;> cases η <;>
    simp [routeLength, segmentOne, segmentTwo, segmentThree, segmentFour,
      segmentFive, paddingIncrease, bit] <;> omega

theorem routeIndex_first (r b : ℕ) (δ η : Bool) (d : ℕ)
    (hr : r = 2 ∨ r = 3) : routeIndex r b δ η d 0 = (false, (r : ℤ)) := by
  have hpos : 0 < segmentOne r δ d := by
    cases δ <;> simp [segmentOne] <;> omega
  simp [routeIndex, hpos]

theorem routeIndex_last (r b : ℕ) (δ η : Bool) (d : ℕ)
    (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b) :
    routeIndex r b δ η d (routeLength r b δ η d - 1) = (false, (b : ℤ)) := by
  cases δ <;> cases η
  all_goals
    simp only [routeIndex, routeLength, segmentOne, segmentTwo, segmentThree,
      segmentFour, segmentFive, highCrossing, lowCrossing, crossingSign, bit,
      Bool.toNat_false, Bool.toNat_true, ↓reduceIte]
    split_ifs <;> simp_all <;> omega

theorem routeIndex_injective (r b : ℕ) (δ η : Bool) (d : ℕ)
    (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b) :
    Function.Injective (fun i : Fin (routeLength r b δ η d) => routeIndex r b δ η d i.val) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  cases δ <;> cases η
  all_goals
    simp only [routeIndex] at hij
    split_ifs at hij <;>
      simp_all [routeLength, segmentOne, segmentTwo, segmentThree, segmentFour,
        segmentFive, lowCrossing, highCrossing, crossingSign, bit] <;> omega

def AvenueBond (a b : Bool × ℤ) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.1 = false ∧ b.1 = true ∧
    ((a.2 % 4 = 0 ∧ b.2 = a.2 - 1) ∨ (a.2 % 4 = 1 ∧ b.2 = a.2 + 1))) ∨
  (a.1 = true ∧ b.1 = false ∧
    ((b.2 % 4 = 0 ∧ a.2 = b.2 - 1) ∨ (b.2 % 4 = 1 ∧ a.2 = b.2 + 1)))

theorem avenueBond_adj (c : Site) (hc : InASublattice c.val) (up : Bool)
    (a b : Bool × ℤ) (h : AvenueBond a b) :
    tetrahedralLattice.Adj (avenueSite c hc up a) (avenueSite c hc up b) := by
  obtain ⟨a, n⟩ := a
  obtain ⟨b, m⟩ := b
  cases a <;> cases b <;> simp only [AvenueBond, avenueSite, ↓reduceIte,
    Bool.false_eq_true, Bool.true_eq_false, and_false, false_and, false_or, or_false,
    true_and, and_true] at h ⊢
  · rcases h with h | h
    · rw [← h]; exact avenue_adj c hc up n
    · rw [← h]; exact (avenue_adj c hc up m).symm
  · rcases h with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · exact crossing_zero c hc up n hn
    · exact crossing_one c hc up n hn
  · rcases h with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
    · exact (crossing_zero c hc up m hm).symm
    · exact (crossing_one c hc up m hm).symm
  · rcases h with h | h
    · rw [← h]; exact secondAvenue_adj c hc up n
    · rw [← h]; exact (secondAvenue_adj c hc up m).symm

theorem routeIndex_consecutive (r b : ℕ) (δ η : Bool) (d i : ℕ)
    (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b)
    (hi : i + 1 < routeLength r b δ η d) :
    AvenueBond (routeIndex r b δ η d i) (routeIndex r b δ η d (i + 1)) := by
  cases δ <;> cases η
  all_goals
    simp only [routeIndex]
    split_ifs <;>
      simp_all [AvenueBond, routeLength, segmentOne, segmentTwo, segmentThree,
        segmentFour, segmentFive, lowCrossing, highCrossing, crossingSign, bit] <;> omega

def paddingFold (c : Site) (hc : InASublattice c.val) (up : Bool)
    (r b : ℕ) (δ η : Bool) (d : ℕ) (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b) :
    Fold tetrahedralLattice (routeLength r b δ η d) where
  pos i := avenueSite c hc up (routeIndex r b δ η d i.val)
  injective_pos := (avenueSite_injective c hc up).comp (routeIndex_injective r b δ η d hr hb)
  consecutive i j hij := by
    apply avenueBond_adj
    rw [← hij]
    exact routeIndex_consecutive r b δ η d i.val hr hb (by omega)

end ProteinFolding.Tetrahedral.FarField
