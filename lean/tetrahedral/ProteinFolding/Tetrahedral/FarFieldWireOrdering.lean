import ProteinFolding.Tetrahedral.FarFieldArmStrips
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Card

/-! Construct the level ordering and slab ordering for an arbitrary finite
wire family. Ranks count distinct coordinate values; slab ties are broken by
the original finite wire index. No sorted-order existence is assumed. -/

namespace ProteinFolding.Tetrahedral.FarField

namespace FiniteRank

variable {w : ℕ} {A : Type} [LinearOrder A]

def values (x : Fin w → A) : Finset A := Finset.univ.image x
def above (x : Fin w → A) (i : Fin w) : Finset A := (values x).filter (fun y => x i < y)
def rank (x : Fin w → A) (i : Fin w) : ℕ := (above x i).card

theorem self_mem (x : Fin w → A) (i : Fin w) : x i ∈ values x := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem rank_lt_of_lt (x : Fin w → A) (i j : Fin w) (h : x i < x j) : rank x j < rank x i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨hy0, hy1⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy0, lt_trans h hy1⟩
  · intro heq
    have hm : x j ∈ above x i := Finset.mem_filter.mpr ⟨self_mem x j, h⟩
    rw [← heq] at hm
    exact lt_irrefl (x j) (Finset.mem_filter.mp hm).2

theorem rank_eq_iff (x : Fin w → A) (i j : Fin w) : rank x i = rank x j ↔ x i = x j := by
  constructor
  · intro h
    rcases lt_trichotomy (x i) (x j) with hij | hij | hji
    · have hlt := rank_lt_of_lt x i j hij
      omega
    · exact hij
    · have hlt := rank_lt_of_lt x j i hji
      omega
  · intro h
    simp [rank, above, h]

theorem rank_lt_count (x : Fin w → A) (i : Fin w) : rank x i < w := by
  have hlt : (above x i).card < (values x).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hm := self_mem x i
    rw [← heq] at hm
    exact lt_irrefl (x i) (Finset.mem_filter.mp hm).2
  have hcard : (values x).card ≤ w := by
    have h := Finset.card_image_le (s := Finset.univ) (f := x)
    simpa only [values, Finset.card_univ, Fintype.card_fin] using h
  exact lt_of_lt_of_le hlt hcard

end FiniteRank

def assignedLevel {w : ℕ} (H : ℤ) (x : Fin w → ℤ) (i : Fin w) : ℤ :=
  H + 4 * FiniteRank.rank x i

theorem assignedLevel_eq_iff {w : ℕ} (H : ℤ) (x : Fin w → ℤ) (i j : Fin w) :
    assignedLevel H x i = assignedLevel H x j ↔ x i = x j := by
  have h := FiniteRank.rank_eq_iff x i j
  unfold assignedLevel
  omega

theorem assignedLevel_reverse_order {w : ℕ} (H : ℤ) (x : Fin w → ℤ) (i j : Fin w)
    (h : assignedLevel H x i < assignedLevel H x j) : x j < x i := by
  rcases lt_trichotomy (x j) (x i) with hij | hij | hji
  · exact hij
  · have heq := (assignedLevel_eq_iff H x i j).2 hij.symm
    omega
  · have hr := FiniteRank.rank_lt_of_lt x i j hji
    unfold assignedLevel at h
    omega

theorem assignedLevel_bounds {w : ℕ} (H : ℤ) (x : Fin w → ℤ) (i : Fin w) :
    H ≤ assignedLevel H x i ∧ assignedLevel H x i ≤ H + 4 * (w - 1 : ℕ) := by
  have hr := FiniteRank.rank_lt_count x i
  unfold assignedLevel
  omega

theorem assignedLevel_separated {w : ℕ} (H : ℤ) (x : Fin w → ℤ) (i j : Fin w)
    (hne : assignedLevel H x i ≠ assignedLevel H x j) :
    assignedLevel H x i + 4 ≤ assignedLevel H x j ∨ assignedLevel H x j + 4 ≤ assignedLevel H x i := by
  unfold assignedLevel at *
  omega

def slabKey {w : ℕ} (levels : Fin w → ℤ) (i : Fin w) : ℤ ×ₗ OrderDual (Fin w) :=
  toLex (levels i, i)

theorem slabKey_injective {w : ℕ} (levels : Fin w → ℤ) : Function.Injective (slabKey levels) := by
  intro i j h
  exact congrArg (fun k : ℤ ×ₗ OrderDual (Fin w) => (ofLex k).2) h

def slabRank {w : ℕ} (levels : Fin w → ℤ) (i : Fin w) : ℕ := FiniteRank.rank (slabKey levels) i

theorem slabRank_injective {w : ℕ} (levels : Fin w → ℤ) : Function.Injective (slabRank levels) := by
  intro i j h
  exact slabKey_injective levels ((FiniteRank.rank_eq_iff (slabKey levels) i j).1 h)

theorem slabRank_lt_count {w : ℕ} (levels : Fin w → ℤ) (i : Fin w) : slabRank levels i < w :=
  FiniteRank.rank_lt_count _ _

theorem slabRank_order {w : ℕ} (levels : Fin w → ℤ) (i j : Fin w) (h : levels j < levels i) :
    slabRank levels i < slabRank levels j := by
  apply FiniteRank.rank_lt_of_lt
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

def slabValue {w : ℕ} (H : ℤ) (levels : Fin w → ℤ) (i : Fin w) : ℤ :=
  H + 60 * (slabRank levels i + 1)

theorem slabValue_bounds {w : ℕ} (H : ℤ) (levels : Fin w → ℤ) (i : Fin w) :
    H + 60 ≤ slabValue H levels i ∧ slabValue H levels i ≤ H + 60 * w := by
  have hr := slabRank_lt_count levels i
  unfold slabValue
  omega

theorem slabValue_order {w : ℕ} (H : ℤ) (levels : Fin w → ℤ) (i j : Fin w) (h : levels j < levels i) :
    slabValue H levels i < slabValue H levels j := by
  have hr := slabRank_order levels i j h
  unfold slabValue
  omega

theorem slabValue_separated {w : ℕ} (H : ℤ) (levels : Fin w → ℤ) (i j : Fin w) (hne : i ≠ j) :
    slabValue H levels i + 60 ≤ slabValue H levels j ∨ slabValue H levels j + 60 ≤ slabValue H levels i := by
  have hr : slabRank levels i ≠ slabRank levels j := fun h => hne (slabRank_injective levels h)
  unfold slabValue
  omega

end ProteinFolding.Tetrahedral.FarField
