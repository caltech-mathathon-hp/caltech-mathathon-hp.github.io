import ProteinFolding.Cubic.Proofs.MatchingPackingSound
import ProteinFolding.Cubic.Proofs.PackingScaling

/-! Total mathematical reduction from raw matching instances to modified
packing. The zero-universe case and malformed coordinate lists are explicit.
The exact-load requirement is essential: adding arbitrary slack to this
construction would lose the real/dummy synchronization argument.

No polynomial-time computation witness is assumed or asserted here. -/

namespace ProteinFolding.MatchingPacking

open ThreeDimensionalMatching NumericPacking

instance wellFormedDecidable (I : ThreeDimensionalMatching.Instance) : Decidable (WellFormed I) :=
  inferInstanceAs (Decidable (∀ t ∈ I.triples,
    t.1 < I.size ∧ t.2.1 < I.size ∧ t.2.2 < I.size))

def yesPacking : Packing.Instance := ⟨[2], 2, 1⟩
def noPacking : Packing.Instance := ⟨[], 1, 1⟩

theorem yesPacking_accepts : Packing.ModifiedAccepts yesPacking := by
  refine ⟨?_, ?_, ?_, [[2]], ?_⟩
  · simp [Packing.WellFormed, yesPacking]
  · simp [yesPacking]
  · rfl
  · simp [Packing.Exact, yesPacking]

theorem noPacking_rejects : ¬ Packing.ModifiedAccepts noPacking := by
  intro h
  have ht := h.2.2.1
  change 0 = 1 at ht
  omega

def toModified (I : ThreeDimensionalMatching.Instance) : Packing.Instance :=
  if WellFormed I then
    if I.size = 0 then yesPacking else Packing.scale 2 (rawInstance I)
  else noPacking

theorem accepts_zero (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (hn : I.size = 0) : Accepts I := by
  refine ⟨hw, [], ?_⟩
  simp [Matches, hn]

/-- Complete yes/no equivalence, on every raw input. The only remaining
obligation for a Karp reduction is its actual polynomial-time machine. -/
theorem toModified_correct (I : ThreeDimensionalMatching.Instance) :
    Accepts I ↔ Packing.ModifiedAccepts (toModified I) := by
  by_cases hw : WellFormed I
  · by_cases hn : I.size = 0
    · simp only [toModified, if_pos hw, if_pos hn]
      exact ⟨fun _ => yesPacking_accepts, fun _ => accepts_zero I hw hn⟩
    · simp only [toModified, if_pos hw, if_neg hn]
      exact (saturated_iff_accepts I hw (by omega)).symm.trans
        (Packing.doubling_iff_modified (rawInstance I))
  · simp only [toModified, if_neg hw]
    constructor
    · intro h
      exact False.elim (hw h.1)
    · intro h
      exact False.elim (noPacking_rejects h)

end ProteinFolding.MatchingPacking
