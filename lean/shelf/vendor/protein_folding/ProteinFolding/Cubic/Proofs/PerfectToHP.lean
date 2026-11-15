import ProteinFolding.Cubic.Proofs.ThresholdCertificateUnarySide
import ProteinFolding.Common.TM2BoundedSearch

/-! Total perfect-to-threshold reduction. The binary side is recovered only
by searching the explicit sequence-length bound. Incorrect H counts are mapped
to a fixed HP no-instance. The proved Theorem 3.2 supplies semantic correctness;
the actual machine implementation is provided in the companion file. -/

namespace ProteinFolding.CubicThresholdReduction

open CubicCertificates TM2BoundedSearch

def sideTest (x : PerfectInput × ℕ) : Bool := decide (x.1.2 = x.2)
def sideBound (I : PerfectInput) : ℕ := I.1.length + 1
def recoveredSide (I : PerfectInput) : ℕ := boundedSearch sideTest (I, sideBound I)

def inputValid (I : PerfectInput) : Bool :=
  decide (I.2 = recoveredSide I) && decide (hydrophobicCount I.1 = recoveredSide I ^ 3)

def noInstance : HPInstance := ⟨[], 1⟩

def reduction (I : PerfectInput) : HPInstance :=
  if inputValid I then ⟨I.1, cubeBondThreshold (recoveredSide I)⟩ else noInstance

theorem recoveredSide_le_bound (I : PerfectInput) : recoveredSide I ≤ I.1.length + 1 :=
  (boundedSearch_spec sideTest I (sideBound I)).1

theorem recoveredSide_eq_of_bounded (I : PerfectInput) (hn : I.2 ≤ I.1.length) :
    recoveredSide I = I.2 := by
  have hs := boundedSearch_spec sideTest I (sideBound I)
  by_cases hsmall : recoveredSide I < I.2
  · have hh := hs.2.1 (show recoveredSide I < sideBound I by unfold sideBound; omega)
    have he : I.2 = recoveredSide I := by simpa only [sideTest, decide_eq_true_eq] using hh
    omega
  · by_cases hlarge : I.2 < recoveredSide I
    · have hh := hs.2.2 I.2 hlarge
      simp only [sideTest, decide_true] at hh
      contradiction
    · omega

theorem inputValid_iff (I : PerfectInput) :
    inputValid I = true ↔ hydrophobicCount I.1 = I.2 ^ 3 := by
  constructor
  · intro h
    have hboth : I.2 = recoveredSide I ∧ hydrophobicCount I.1 = recoveredSide I ^ 3 := by
      simpa only [inputValid, Bool.and_eq_true, decide_eq_true_eq] using h
    obtain ⟨hs, hc⟩ := hboth
    simpa only [← hs] using hc
  · intro hc
    have hside := recoveredSide_eq_of_bounded I (side_le_sequence_length_of_count I hc)
    simp [inputValid, hside, hc]

theorem noInstance_rejects : ¬ noInstance.Accepts := by
  rintro ⟨f, hf⟩
  change (1 : ℤ) ≤ (bondCount [] f : ℤ) at hf
  simp [bondCount, hhBonds] at hf

theorem reduction_eq_threshold (I : PerfectInput) (hc : hydrophobicCount I.1 = I.2 ^ 3) :
    reduction I = thresholdInstance I := by
  have hv := (inputValid_iff I).mpr hc
  have hs := recoveredSide_eq_of_bounded I (side_le_sequence_length_of_count I hc)
  simp only [reduction, hv, ↓reduceIte, hs, thresholdInstance]

/-- On all raw inputs, including malformed binary sides and wrong H counts,
the new total map preserves exactly the frozen perfect-folding predicate. -/
theorem reduction_correct (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ (reduction I).Accepts := by
  by_cases hc : hydrophobicCount I.1 = I.2 ^ 3
  · rw [reduction_eq_threshold I hc]
    change (hydrophobicCount I.1 = I.2 ^ 3 ∧ ∃ f, PacksCube I.1 f I.2) ↔
      ∃ f : Fold cubicLattice I.1.length, cubeBondThreshold I.2 ≤ (bondCount I.1 f : ℤ)
    simp only [hc, true_and]
    exact exists_congr (fun f => CubicGeometry.packsCube_iff_bond_threshold I.1 f I.2 hc)
  · have hv : inputValid I = false := Bool.eq_false_iff.mpr (fun h => hc ((inputValid_iff I).mp h))
    simp only [PerfectHPStringFold, hc, false_and, reduction, hv, Bool.false_eq_true, if_false]
    exact iff_of_false (by simp) noInstance_rejects

end ProteinFolding.CubicThresholdReduction
