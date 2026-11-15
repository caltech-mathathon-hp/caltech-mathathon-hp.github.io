import ProteinFolding.Tetrahedral.ConstructionParameters

/-! The uniform numerical budgets in Lemma F(E). The path constructions and
their disjointness are proved separately; these lemmas preserve the exact
constants of the word and convert a base-length bound to a padding budget. -/

namespace ProteinFolding.Tetrahedral

def farFieldHeight (m : ℕ) : ℕ := 20 * m + 21
def farFieldMaxLevel (m w : ℕ) : ℕ := farFieldHeight m + 6 * w + 8
def farFieldWireLevel (m r : ℕ) : ℕ := farFieldHeight m + 4 * r
def farFieldJoinLevel (m w i : ℕ) : ℕ := farFieldHeight m + 4 * w + 8 + 4 * i

def farFieldBaseBound (m w : ℕ) : ℕ :=
  2 * ((farFieldMaxLevel m w + 2) + (2 * farFieldHeight m + 60 * w + 3) +
    (4 * farFieldMaxLevel m w + 4)) + (60 * w + 13) + 1

def farFieldLengthThreshold (m w : ℕ) : ℕ := 1000 * (m + w + 1) + 6

theorem farFieldBaseBound_formula (m w : ℕ) :
    farFieldBaseBound m w = 280 * m + 240 * w + 406 := by
  unfold farFieldBaseBound farFieldMaxLevel farFieldHeight
  ring

theorem farFieldBaseBound_lt_budget (m w : ℕ) :
    farFieldBaseBound m w < 1000 * (m + w + 1) := by
  rw [farFieldBaseBound_formula]
  omega

theorem farField_nearField_separation (m K : ℕ) (hK : K ≤ m) :
    2 * m + 8 * K + 12 < farFieldHeight m := by
  unfold farFieldHeight
  omega

theorem farField_initial_column_separation (m : ℕ) :
    2 * m + 4 < farFieldHeight m := by
  unfold farFieldHeight
  omega

theorem farField_wire_below_join (m w r : ℕ) (hr : r < w) :
    farFieldWireLevel m r + 4 < farFieldJoinLevel m w 0 := by
  unfold farFieldWireLevel farFieldJoinLevel
  omega

theorem farField_join_level_bound (m w i : ℕ) (hi : 2 * i ≤ w) :
    farFieldJoinLevel m w i ≤ farFieldMaxLevel m w := by
  unfold farFieldJoinLevel farFieldMaxLevel
  omega

theorem farField_private_levels_separated (m w i j : ℕ) (hij : i < j) :
    farFieldJoinLevel m w i + 2 < farFieldJoinLevel m w j := by
  unfold farFieldJoinLevel
  omega

theorem farFieldLengthThreshold_even (m w : ℕ) :
    farFieldLengthThreshold m w % 2 = 0 := by
  unfold farFieldLengthThreshold
  omega

/-- An arbitrary allowed linker length leaves enough room for the explicit
all-residue-class padding, once its base path has the proved uniform bound. -/
theorem farField_padding_budget (m w β L : ℕ)
    (hβ : β ≤ farFieldBaseBound m w) (hL : farFieldLengthThreshold m w ≤ L)
    (hparity : L % 2 = β % 2) :
    ∃ Δ : ℕ, 6 ≤ Δ ∧ Δ % 2 = 0 ∧ β + Δ = L := by
  have hb := farFieldBaseBound_lt_budget m w
  unfold farFieldLengthThreshold at hL
  refine ⟨L - β, ?_, ?_, ?_⟩ <;> omega

theorem ConstructionParameters.baseLinkerLength_eq_threshold (p : ConstructionParameters)
    (w : ℕ) : p.baseLinkerLength w = farFieldLengthThreshold p.side w := rfl

end ProteinFolding.Tetrahedral
