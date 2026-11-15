import ProteinFolding.Cubic.Proofs.ThresholdCertificateRecords
import ProteinFolding.Cubic.Proofs.VerifierHPSemantics
import ProteinFolding.Cubic.Proofs.VerifierValidity

/-! Exact semantic bridge from the total four-bit decoder and all-pairs
geometric scan to the frozen perfect folding problem. -/

namespace ProteinFolding.CubicCertificates

open CubicVerifier CubicRecordDecoder CubicHPVerifier

theorem perfectRecordBitsAccept_iff_geometry (I : PerfectInput) (w : List Bool) :
    PerfectRecordBitsAccept (I, w) ↔
      hydrophobicCount I.1 = I.2 ^ 3 ∧ I.1 = decodedLabels w ∧
        geometryValid (stream w) = true ∧
          bondCountRecords (stream w) = 3 * I.2 ^ 2 * (I.2 - 1) := by
  constructor
  · intro h
    unfold PerfectRecordBitsAccept at h
    cases hd : decodeRecords w with
    | none => simp [hd] at h
    | some rs =>
      simp only [hd] at h
      have hs : stream w = rs.map some := (collectRecords_eq_some_iff _ rs).mp hd
      obtain ⟨hc, hscore⟩ := h
      cases hf : recordFold I.1 rs with
      | none => simp [hf] at hscore
      | some f =>
        simp only [hf] at hscore
        have hv := validRecords_of_recordFold_some I.1 rs f hf
        refine ⟨hc, ?_, ?_, ?_⟩
        · simpa [decodedLabels, hs, List.filterMap_map, Function.comp_def] using hv.1.symm
        · rw [hs]
          exact (geometryValid_records_iff rs).mpr (injective_of_validRecords I.1 rs hv)
        · rw [hs, recordFold_bondCountRecords I.1 rs f hf]
          exact hscore
  · rintro ⟨hc, hlabels, hvalid, hscore⟩
    obtain ⟨rs, hs⟩ := geometryValid_some (stream w) hvalid
    have hls : rs.map Prod.fst = I.1 := by
      simpa [decodedLabels, hs, List.filterMap_map, Function.comp_def] using hlabels.symm
    have hinj := (geometryValid_records_iff rs).mp (by simpa only [hs] using hvalid)
    have hv := validRecords_of_injective I.1 rs hls hinj
    obtain ⟨f, hf⟩ := recordFold_exists_of_valid I.1 rs hv
    have hd : decodeRecords w = some rs := (collectRecords_eq_some_iff _ rs).mpr hs
    simp only [PerfectRecordBitsAccept, hd, PerfectRecordsAccept, hf]
    refine ⟨hc, ?_⟩
    rw [hs, recordFold_bondCountRecords I.1 rs f hf] at hscore
    exact hscore

end ProteinFolding.CubicCertificates
