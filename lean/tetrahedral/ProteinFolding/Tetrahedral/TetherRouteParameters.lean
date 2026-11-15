import ProteinFolding.Tetrahedral.WordPieces

/-! Exact skin indices and site-count arithmetic of the explicit N4 routes.
The separator parameter k is zero based. These count the prescribed row and
column pieces; actual paths and their disjointness are separate geometry. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

def entrySkin (_p : ConstructionParameters) (k : ℕ) : ℕ := k + 2
def exitSkin (p : ConstructionParameters) (k : ℕ) : ℕ := p.bins + k + 3
def exitSlot (p : ConstructionParameters) (k : ℕ) : ℕ := p.bins - k

def entryRouteSiteCount (p : ConstructionParameters) (k : ℕ) : ℕ :=
  (2 * p.entrySkin k - 2) + 1 + 1 + 2 * (3 * (k + 1) + 1) +
    2 * p.separatorIndex k + 1 + (2 * p.entrySkin k - 2)

def exitRouteSiteCount (p : ConstructionParameters) (k : ℕ) : ℕ :=
  (2 * p.exitSkin k - 2) + 1 + 1 + 2 * (p.side - 2 - p.separatorIndex k) +
    2 * (5 * p.exitSlot k + 4) + 1 + (2 * p.exitSkin k - 2)

theorem entryRouteSiteCount_eq_tether (p : ConstructionParameters) (k : ℕ) :
    p.entryRouteSiteCount k = p.entryTether k := by
  unfold entryRouteSiteCount entrySkin entryTether entrySlack
  omega

theorem exitRouteSiteCount_eq_tether (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) : p.exitRouteSiteCount k = p.exitTether k := by
  unfold exitRouteSiteCount exitSkin exitSlot exitTether exitSlack
  omega

theorem tether_skin_bounds (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    2 ≤ p.entrySkin k ∧ p.entrySkin k ≤ p.bins + 2 ∧
      p.bins + 3 ≤ p.exitSkin k ∧ p.exitSkin k ≤ 2 * p.bins + 3 := by
  unfold entrySkin exitSkin
  omega

theorem entrySkins_injective (p : ConstructionParameters) : Function.Injective p.entrySkin := by
  intro k l h
  unfold entrySkin at h
  omega

theorem exitSkins_injective (p : ConstructionParameters) : Function.Injective p.exitSkin := by
  intro k l h
  unfold exitSkin at h
  omega

theorem entrySkin_lt_exitSkin (p : ConstructionParameters) (k l : ℕ) (hk : k ≤ p.bins) :
    p.entrySkin k < p.exitSkin l := by
  unfold entrySkin exitSkin
  omega

theorem entry_column_triangle_room (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    3 * (k + 1) + 6 ≤ p.side := by
  have h := p.family_side_bound
  omega

theorem exit_column_triangle_room (p : ConstructionParameters) (k : ℕ) :
    5 * p.exitSlot k + 8 ≤ p.side := by
  have h := p.family_side_bound
  unfold exitSlot
  omega

theorem exitSlot_add (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    p.exitSlot k + k = p.bins := by
  unfold exitSlot
  omega

end ProteinFolding.Tetrahedral.ConstructionParameters
