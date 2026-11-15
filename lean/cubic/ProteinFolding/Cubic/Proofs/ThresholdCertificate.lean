import ProteinFolding.Cubic.Proofs.CertificatesPerfect
import ProteinFolding.Cubic.Proofs.GeometryMain
import ProteinFolding.Common.ComplexityLemmas

/-! Reusing the HP contact checker for the perfect-packing verifier.
The proved geometric theorem replaces cube enumeration by an H-count guard
and a bond threshold, on exactly the same direction certificate. -/

namespace ProteinFolding.CubicCertificates

def thresholdInstance (I : PerfectInput) : HPInstance :=
  ⟨I.1, cubeBondThreshold I.2⟩

def ThresholdBitsAccepts (input : PerfectInput × List Bool) : Prop :=
  hydrophobicCount input.1.1 = input.1.2 ^ 3 ∧
    BitsAccepts (thresholdInstance input.1, input.2)

instance (input : PerfectInput × List Bool) : Decidable (ThresholdBitsAccepts input) := by
  unfold ThresholdBitsAccepts
  infer_instance

theorem perfectDirectionAccepts_iff_threshold (I : PerfectInput) (ds : DirectionWord) :
    PerfectDirectionAccepts (I, ds) ↔
      hydrophobicCount I.1 = I.2 ^ 3 ∧ DirectionAccepts (thresholdInstance I, ds) := by
  by_cases hc : hydrophobicCount I.1 = I.2 ^ 3
  · simp only [PerfectDirectionAccepts, thresholdInstance, DirectionAccepts,
      hc, true_and]
    cases hfold : certificateFold I.1 ds with
    | none => rfl
    | some f =>
      exact (finitePacksCube_iff I.1 f I.2).trans
        (CubicGeometry.packsCube_iff_bond_threshold I.1 f I.2 hc)
  · simp only [PerfectDirectionAccepts, hc, false_and]

theorem perfectBitsAccepts_iff_threshold (input : PerfectInput × List Bool) :
    PerfectBitsAccepts input ↔ ThresholdBitsAccepts input := by
  obtain ⟨I, w⟩ := input
  unfold PerfectBitsAccepts ThresholdBitsAccepts BitsAccepts
  cases hdecode : decodeDirections w with
  | none => simp
  | some ds => exact perfectDirectionAccepts_iff_threshold I ds

/-- An executable exact replacement for the finite-cube enumerator. Its
machine-level runtime is a separate obligation below. -/
def thresholdPerfectBitsVerifier (input : PerfectInput × List Bool) : Bool :=
  decide (ThresholdBitsAccepts input)

theorem thresholdPerfectBitsVerifier_spec (input : PerfectInput × List Bool) :
    thresholdPerfectBitsVerifier input = true ↔ PerfectBitsAccepts input := by
  simpa only [thresholdPerfectBitsVerifier, decide_eq_true_eq] using
    (perfectBitsAccepts_iff_threshold input).symm

theorem perfect_threshold_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ w : List Bool,
      w.length = 3 * I.1.length ∧ ThresholdBitsAccepts (I, w) := by
  rw [perfect_bits_certificate_iff]
  constructor
  · rintro ⟨w, hlen, hw⟩
    exact ⟨w, hlen, (perfectBitsAccepts_iff_threshold (I, w)).mp hw⟩
  · rintro ⟨w, hlen, hw⟩
    exact ⟨w, hlen, (perfectBitsAccepts_iff_threshold (I, w)).mpr hw⟩

/-- This result deliberately exposes the remaining machine proof. It is not
an unconditional membership theorem. -/
theorem perfect_inNP_of_threshold_verifier_polyTime
    (h : PolyTimeDecidable (pairEncoding perfectEncoding (wordEncoding Bool))
      ThresholdBitsAccepts) :
    InNP perfectEncoding (fun I => PerfectHPStringFold I.1 I.2) := by
  apply perfect_inNP_of_bits_verifier_polyTime
  exact polyTimeDecidable_congr (fun input => (perfectBitsAccepts_iff_threshold input).symm) h

end ProteinFolding.CubicCertificates
