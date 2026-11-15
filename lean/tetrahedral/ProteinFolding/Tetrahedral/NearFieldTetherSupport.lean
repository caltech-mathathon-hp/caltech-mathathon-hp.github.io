import ProteinFolding.Tetrahedral.NearFieldEntryTethers
import ProteinFolding.Tetrahedral.NearFieldExitTethers

/-! Exact support decompositions of the two assembled tether constructors. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem entryTetherRaw_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hup : ∀ i, P ((entryUp p k hk).pos i))
    (hrow : ∀ i, P ((entryRowFold p k hk).pos i)) (hdown : ∀ i, P ((entryDown p k hk).pos i))
    (i : Fin (((2 * p.entrySkin k - 1) + entryRowCount p k) + (2 * p.entrySkin k - 1))) :
    P ((entryTetherRaw p k hk).pos i) := by
  unfold entryTetherRaw
  apply append_property _ _ _ _ P ?_ hdown i
  intro r
  exact append_property _ _ _ _ P hup hrow r

theorem entryTetherFold_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hup : ∀ i, P ((entryUp p k hk).pos i))
    (hrow : ∀ i, P ((entryRowFold p k hk).pos i)) (hdown : ∀ i, P ((entryDown p k hk).pos i))
    (i : Fin (p.entryTether k)) : P ((entryTetherFold p k hk).pos i) :=
  entryTetherRaw_property p k hk P hup hrow hdown _

theorem exitTetherRaw_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hup : ∀ i, P ((exitUp p k hk).pos i))
    (hrow : ∀ i, P ((exitRowFold p k hk).pos i)) (hdown : ∀ i, P ((exitDown p k).pos i))
    (i : Fin ((exitColumnCount p k + exitRowCount p k) + exitColumnCount p k)) :
    P ((exitTetherRaw p k hk).pos i) := by
  unfold exitTetherRaw
  apply append_property _ _ _ _ P ?_ hdown i
  intro r
  exact append_property _ _ _ _ P hup hrow r

theorem exitTetherFold_property (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (P : Site → Prop) (hup : ∀ i, P ((exitUp p k hk).pos i))
    (hrow : ∀ i, P ((exitRowFold p k hk).pos i)) (hdown : ∀ i, P ((exitDown p k).pos i))
    (i : Fin (p.exitTether k)) : P ((exitTetherFold p k hk).pos i) :=
  exitTetherRaw_property p k hk P hup hrow hdown _

theorem positiveSkin_outside (m j : ℕ) (hj : 1 ≤ j) {q : Site} (hq : q ∈ skin m j) :
    q ∉ octahedron m := by
  intro hoct
  apply (Finset.mem_sdiff.mp hq).2
  apply skinSolid_mono m (show 0 ≤ j - 1 by omega)
  simpa only [skinSolid_zero] using hoct

end ProteinFolding.Tetrahedral.NearField
