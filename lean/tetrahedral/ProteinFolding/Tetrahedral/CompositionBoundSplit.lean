import ProteinFolding.Tetrahedral.ProfileComposition
import ProteinFolding.Tetrahedral.RootConvexity

/-! Structural splitting at a median, allowing empty prefix and suffix honestly. -/

namespace ProteinFolding.Tetrahedral

open PositiveComposition

def medianContextMass : Option PositiveComposition → ℕ
  | none => 0
  | some c => c.mass

def medianLeft (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b) : PositiveComposition :=
  match pre with
  | none => .single b hb
  | some p => .snoc p b hb

def medianRight (suf : Option PositiveComposition) (b : ℕ) (hb : 0 < b) : PositiveComposition :=
  match suf with
  | none => .single b hb
  | some q => .snoc q.reverse b hb

def medianBuild (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
    (suf : Option PositiveComposition) : PositiveComposition :=
  match suf with
  | none => medianLeft pre b hb
  | some q => (medianLeft pre b hb).append q

def medianExtend (suf : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    Option PositiveComposition :=
  some (match suf with | none => .single b hb | some q => .snoc q b hb)

theorem medianLeft_mass (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianLeft pre b hb).mass = medianContextMass pre + b := by
  cases pre <;> simp [medianLeft, medianContextMass, mass]

theorem medianRight_mass (suf : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianRight suf b hb).mass = medianContextMass suf + b := by
  cases suf <;> simp [medianRight, medianContextMass, mass, reverse_mass]

theorem medianLeft_last (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianLeft pre b hb).lastPart = b := by cases pre <;> rfl

theorem medianRight_last (suf : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianRight suf b hb).lastPart = b := by cases suf <;> rfl

theorem medianBuild_mass (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
    (suf : Option PositiveComposition) :
    (medianBuild pre b hb suf).mass = medianContextMass pre + b + medianContextMass suf := by
  cases suf <;> simp [medianBuild, medianContextMass, medianLeft_mass, append_mass]

theorem medianBuild_extend (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
    (suf : Option PositiveComposition) (d : ℕ) (hd : 0 < d) :
    medianBuild pre b hb (medianExtend suf d hd) = .snoc (medianBuild pre b hb suf) d hd := by
  cases suf <;> rfl

/-- Either a median is a breakpoint, or it lies strictly inside one part. -/
theorem composition_median_split (c : PositiveComposition) (M : ℕ)
    (hM : 0 < M) (hbelow : M < c.mass) :
    (∃ L R : PositiveComposition, c = L.append R ∧ L.mass = M) ∨
    (∃ (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
      (suf : Option PositiveComposition), c = medianBuild pre b hb suf ∧
        medianContextMass pre < M ∧ M < medianContextMass pre + b) := by
  induction c generalizing M with
  | single b hb =>
    exact Or.inr ⟨none, b, hb, none, rfl, hM,
      by simpa [medianContextMass, mass] using hbelow⟩
  | snoc c d hd ih =>
    change M < c.mass + d at hbelow
    by_cases hbefore : M < c.mass
    · rcases ih M hM hbefore with ⟨L, R, heq, hmass⟩ | ⟨pre, b, hb, suf, heq, hleft, hright⟩
      · exact Or.inl ⟨L, .snoc R d hd, by rw [heq]; rfl, hmass⟩
      · refine Or.inr ⟨pre, b, hb, medianExtend suf d hd, ?_, hleft, hright⟩
        rw [medianBuild_extend, ← heq]
    · by_cases heq : M = c.mass
      · exact Or.inl ⟨c, .single d hd, rfl, heq.symm⟩
      · exact Or.inr ⟨some c, d, hd, none, rfl, by change c.mass < M; omega, hbelow⟩

/-- Splitting at a breakpoint bounds the two sides by their one-sided values. -/
theorem twoSidedValue_append_le (L R : PositiveComposition) :
    twoSidedValue (L.append R) ≤ L.value +
      min (min L.mass R.mass) (L.lastPart * R.firstPart) + R.reverse.value := by
  let C := L.mass + R.mass
  have hL := profileValue_le_oneSided C L
  have hR : profileValue C L.mass R ≤ R.reverse.value := by
    have hmirror := profileValue_mirror C L.mass R (by dsimp [C]; omega)
    have hzero : C - L.mass - R.mass = 0 := by dsimp [C]; omega
    rw [hzero] at hmirror
    rw [hmirror]
    exact profileValue_le_oneSided C R.reverse
  unfold twoSidedValue
  rw [append_mass, profileValue_append]
  simp only [Nat.zero_add]
  have hrem : L.mass + R.mass - L.mass = R.mass := by omega
  rw [hrem]
  change profileValue C 0 L + min (min L.mass R.mass) (L.lastPart * R.firstPart) +
    profileValue C L.mass R ≤ _
  omega

/-- The two overlapping one-sided compositions cover every original breakpoint. -/
theorem medianBuild_value_le (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b)
    (suf : Option PositiveComposition) :
    twoSidedValue (medianBuild pre b hb suf) ≤
      (medianLeft pre b hb).value + (medianRight suf b hb).value := by
  cases suf with
  | none =>
    simpa only [medianBuild, medianRight, value, Nat.add_zero, twoSidedValue] using
      profileValue_le_oneSided (medianLeft pre b hb).mass (medianLeft pre b hb)
  | some R =>
    have h := twoSidedValue_append_le (medianLeft pre b hb) R
    rw [medianLeft_last] at h
    have hmin : min (min (medianLeft pre b hb).mass R.mass) (b * R.firstPart) ≤
        min R.mass (R.firstPart * b) := by
      rw [Nat.mul_comm b R.firstPart]
      exact min_le_min (min_le_right _ _) le_rfl
    change twoSidedValue ((medianLeft pre b hb).append R) ≤
      (medianLeft pre b hb).value + (R.reverse.value + min R.reverse.mass (R.reverse.lastPart * b))
    rw [reverse_mass, reverse_last]
    omega

theorem medianLeft_value_le_rootG (pre : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianLeft pre b hb).value ≤ rootG (medianContextMass pre) := by
  cases pre with
  | none => simp [medianLeft, value, medianContextMass]
  | some p =>
    have h := oneSided_le_rootSum p
    have hmin := min_le_left p.mass (p.lastPart * b)
    change p.value + min p.mass (p.lastPart * b) ≤ rootSum p.mass + p.mass
    omega

theorem medianRight_value_le_rootG (suf : Option PositiveComposition) (b : ℕ) (hb : 0 < b) :
    (medianRight suf b hb).value ≤ rootG (medianContextMass suf) := by
  cases suf with
  | none => simp [medianRight, value, medianContextMass]
  | some q =>
    have h := oneSided_le_rootSum q.reverse
    rw [reverse_mass] at h
    have hmin := min_le_left q.reverse.mass (q.reverse.lastPart * b)
    rw [reverse_mass] at hmin
    change q.reverse.value + min q.reverse.mass (q.reverse.lastPart * b) ≤ rootSum q.mass + q.mass
    rw [reverse_mass]
    omega

/-- On the left half of the total interval the far-end cap is inactive. -/
theorem profileValue_eq_oneSided_of_double_mass_le (C : ℕ) (c : PositiveComposition)
    (hsize : 2 * c.mass ≤ C) : profileValue C 0 c = c.value := by
  induction c with
  | single p hp => rfl
  | snoc p b hb ih =>
    have hp : 2 * p.mass ≤ C := by change 2 * (p.mass + b) ≤ C at hsize; omega
    have hcap : p.mass ≤ C - p.mass := by omega
    simp only [profileValue, value, Nat.zero_add, min_eq_left hcap]
    rw [ih hp]

end ProteinFolding.Tetrahedral
