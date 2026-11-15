import ProteinFolding.Tetrahedral.LocalStructure
import ProteinFolding.Tetrahedral.Layers

/-!
# The oriented zigzags in a layer gap

For gap k, containing layers k and k+1, orient every zigzag by increasing y.
`gapNext` and `gapPrev` are defined on all sites; on that gap they stay in the
same gap. They are mutual inverses, change y by exactly one, and preserve the
chain key y-z (even k) or y+z (odd k).
-/

namespace ProteinFolding.Tetrahedral


theorem inA_iff_x_even (p : Site) : InASublattice p.val ↔ p.val 0 % 2 = 0 := by
  constructor
  · exact fun hp => hp.1 0
  · intro hx
    rcases p.property with hp | hp
    · exact hp
    · have h := hp.1 0
      omega

def InGap (k : ℤ) (p : Site) : Prop := p.val 0 = k ∨ p.val 0 = k + 1

instance decidableInGap (k : ℤ) : DecidablePred (InGap k) := fun p =>
  inferInstanceAs (Decidable (p.val 0 = k ∨ p.val 0 = k + 1))

def gapNext (k : ℤ) (p : Site) : Site :=
  step p (if k % 2 = 0 then if InASublattice p.val then 0 else 1
    else if InASublattice p.val then 2 else 3)

def gapPrev (k : ℤ) (p : Site) : Site :=
  step p (if k % 2 = 0 then if InASublattice p.val then 1 else 0
    else if InASublattice p.val then 3 else 2)

def gapSlope (k : ℤ) : ℤ := if k % 2 = 0 then 1 else -1

def gapOtherX (k : ℤ) (p : Site) : ℤ :=
  if k % 2 = 0 then if InASublattice p.val then p.val 0 + 1 else p.val 0 - 1
  else if InASublattice p.val then p.val 0 - 1 else p.val 0 + 1


theorem gapNext_val (k : ℤ) (p : Site) :
    (gapNext k p).val = ![gapOtherX k p, p.val 1 + 1, p.val 2 + gapSlope k] := by
  by_cases hk : k % 2 = 0 <;> by_cases hp : InASublattice p.val
  all_goals simp only [gapNext, gapOtherX, gapSlope, hk, hp, if_true, if_false]
  all_goals first
    | rw [step_val_of_A p hp]
    | rw [step_val_of_B p ((inB_iff_not_inA p).mpr hp)]
  all_goals
    funext i
    fin_cases i <;> rfl


theorem gapPrev_val (k : ℤ) (p : Site) :
    (gapPrev k p).val = ![gapOtherX k p, p.val 1 - 1, p.val 2 - gapSlope k] := by
  by_cases hk : k % 2 = 0 <;> by_cases hp : InASublattice p.val
  all_goals simp only [gapPrev, gapOtherX, gapSlope, hk, hp, if_true, if_false]
  all_goals first
    | rw [step_val_of_A p hp]
    | rw [step_val_of_B p ((inB_iff_not_inA p).mpr hp)]
  all_goals
    funext i
    fin_cases i <;> rfl

theorem gapNext_adj (k : ℤ) (p : Site) : tetrahedralLattice.Adj p (gapNext k p) :=
  step_adj p _

theorem gapPrev_adj (k : ℤ) (p : Site) : tetrahedralLattice.Adj p (gapPrev k p) :=
  step_adj p _

@[simp] theorem gapPrev_next (k : ℤ) (p : Site) : gapPrev k (gapNext k p) = p := by
  have hc := adj_not_same_sublattice (gapNext_adj k p).symm
  by_cases hk : k % 2 = 0 <;> by_cases hp : InASublattice p.val
  all_goals
    have hq : InASublattice (gapNext k p).val ↔ ¬ InASublattice p.val := hc
    simp only [hp, not_true_eq_false, not_false_eq_true, iff_false, iff_true] at hq
    simp only [gapPrev, hq, hk, if_true, if_false]
    simp [gapNext, hk, hp]

@[simp] theorem gapNext_prev (k : ℤ) (p : Site) : gapNext k (gapPrev k p) = p := by
  have hc := adj_not_same_sublattice (gapPrev_adj k p).symm
  by_cases hk : k % 2 = 0 <;> by_cases hp : InASublattice p.val
  all_goals
    have hq : InASublattice (gapPrev k p).val ↔ ¬ InASublattice p.val := hc
    simp only [hp, not_true_eq_false, not_false_eq_true, iff_false, iff_true] at hq
    simp only [gapNext, hq, hk, if_true, if_false]
    simp [gapPrev, hk, hp]

theorem gapNext_injective (k : ℤ) : Function.Injective (gapNext k) :=
  Function.LeftInverse.injective (gapPrev_next k)

theorem gapPrev_injective (k : ℤ) : Function.Injective (gapPrev k) :=
  Function.LeftInverse.injective (gapNext_prev k)


theorem gapOtherX_in_gap {k : ℤ} {p : Site} (hp : InGap k p) :
    gapOtherX k p = 2 * k + 1 - p.val 0 := by
  rcases hp with hx | hx
  · have hcol : InASublattice p.val ↔ k % 2 = 0 := by rw [inA_iff_x_even, hx]
    by_cases hk : k % 2 = 0
    · simp [gapOtherX, hk, hcol.mpr hk, hx]
      omega
    · have hA : ¬ InASublattice p.val := fun hA => hk (hcol.mp hA)
      simp [gapOtherX, hk, hA, hx]
      omega
  · by_cases hk : k % 2 = 0
    · have hA : ¬ InASublattice p.val := by
        intro hA
        have he := (inA_iff_x_even p).mp hA
        omega
      simp [gapOtherX, hk, hA, hx]
      omega
    · have hA : InASublattice p.val := (inA_iff_x_even p).mpr (by omega)
      simp [gapOtherX, hk, hA, hx]
      omega


theorem gapNext_in_gap {k : ℤ} {p : Site} (hp : InGap k p) : InGap k (gapNext k p) := by
  have hx := gapOtherX_in_gap hp
  have hn := congrFun (gapNext_val k p) 0
  simp only [Matrix.cons_val_zero] at hn
  rcases hp with hp | hp <;> unfold InGap <;> omega

theorem gapPrev_in_gap {k : ℤ} {p : Site} (hp : InGap k p) : InGap k (gapPrev k p) := by
  have hx := gapOtherX_in_gap hp
  have hn := congrFun (gapPrev_val k p) 0
  simp only [Matrix.cons_val_zero] at hn
  rcases hp with hp | hp <;> unfold InGap <;> omega

@[simp] theorem gapNext_y (k : ℤ) (p : Site) : (gapNext k p).val 1 = p.val 1 + 1 := by
  simp [gapNext_val]

@[simp] theorem gapPrev_y (k : ℤ) (p : Site) : (gapPrev k p).val 1 = p.val 1 - 1 := by
  simp [gapPrev_val]

def gapChainKey (k : ℤ) (p : Site) : ℤ :=
  if k % 2 = 0 then p.val 1 - p.val 2 else p.val 1 + p.val 2

@[simp] theorem gapNext_key (k : ℤ) (p : Site) :
    gapChainKey k (gapNext k p) = gapChainKey k p := by
  by_cases hk : k % 2 = 0 <;> simp [gapChainKey, gapNext_val, gapSlope, hk] <;> omega

@[simp] theorem gapPrev_key (k : ℤ) (p : Site) :
    gapChainKey k (gapPrev k p) = gapChainKey k p := by
  by_cases hk : k % 2 = 0 <;> simp [gapChainKey, gapPrev_val, gapSlope, hk]

end ProteinFolding.Tetrahedral
