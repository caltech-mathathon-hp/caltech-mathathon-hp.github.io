import ProteinFolding.Cubic.Proofs.VerifierHP
import ProteinFolding.Cubic.Proofs.VerifierPairCount
import ProteinFolding.Cubic.Proofs.VerifierValidity
import ProteinFolding.Common.ComplexityBoolean

/-! Semantic seams for the HP verifier. The final validity equivalence is
provided by the geometric all-suffix proof; no complexity hypothesis is used
in these conversions between record positions and frozen folds. -/

namespace ProteinFolding.CubicHPVerifier

open Computability Turing CubicVerifier CubicRecordDecoder

theorem validRecords_of_injective (S : Sequence) (rs : List Record)
    (hlabels : rs.map Prod.fst = S)
    (hinj : Function.Injective (fun i : Fin rs.length => recordPosition rs i.val)) :
    ValidRecords S rs := by
  refine ⟨hlabels, ?_⟩
  have hlen := record_labels_length hlabels
  intro i j hij
  let ir : Fin rs.length := ⟨i.val, by have := i.isLt; omega⟩
  let jr : Fin rs.length := ⟨j.val, by have := j.isLt; omega⟩
  have he : recordPosition rs ir.val = recordPosition rs jr.val := hij
  have heq : ir = jr := hinj he
  exact Fin.ext (congrArg (fun k : Fin rs.length => k.val) heq)

theorem injective_of_validRecords (S : Sequence) (rs : List Record) (hv : ValidRecords S rs) :
    Function.Injective (fun i : Fin rs.length => recordPosition rs i.val) := by
  have hlen := record_labels_length hv.1
  intro i j hij
  let ir : Fin S.length := ⟨i.val, by have := i.isLt; omega⟩
  let jr : Fin S.length := ⟨j.val, by have := j.isLt; omega⟩
  have he : recordPosition rs ir.val = recordPosition rs jr.val := hij
  have heq : ir = jr := hv.2 he
  exact Fin.ext (congrArg (fun k : Fin S.length => k.val) heq)

theorem recordFold_exists_of_valid (S : Sequence) (rs : List Record) (hv : ValidRecords S rs) :
    ∃ f, recordFold S rs = some f := by
  unfold recordFold
  split
  · exact ⟨_, rfl⟩
  · contradiction

theorem validRecords_of_recordFold_some (S : Sequence) (rs : List Record)
    (f : Fold cubicLattice S.length) (hf : recordFold S rs = some f) : ValidRecords S rs := by
  by_contra hn
  simp [recordFold, hn] at hf

theorem verify_sound (I : HPInstance) (w : List Bool) (hw : verify (I, w) = true) : I.Accepts := by
  obtain ⟨hlabels, hgeo, hthreshold⟩ := (verify_correct (I, w)).mp hw
  obtain ⟨rs, hrs⟩ := geometryValid_some (stream w) hgeo
  have hlabelsRS : rs.map Prod.fst = I.sequence := by
    simpa [decodedLabels, hrs, List.filterMap_map, Function.comp_def] using hlabels.symm
  have hinj : Function.Injective (fun i : Fin rs.length => recordPosition rs i.val) := by
    apply (geometryValid_records_iff rs).mp
    simpa only [hrs] using hgeo
  have hv := validRecords_of_injective I.sequence rs hlabelsRS hinj
  obtain ⟨f, hf⟩ := recordFold_exists_of_valid I.sequence rs hv
  have hscore := recordFold_bondCountRecords I.sequence rs f hf
  refine ⟨f, ?_⟩
  simpa only [hrs, hscore] using hthreshold

theorem verify_encodeRecords (I : HPInstance) (rs : List Record)
    (hacc : RecordsAccept (I, rs)) : verify (I, encodeRecords rs) = true := by
  have hv : ValidRecords I.sequence rs := by
    by_contra hn
    simp [RecordsAccept, recordFold, hn] at hacc
  obtain ⟨f, hf⟩ := recordFold_exists_of_valid I.sequence rs hv
  have hthreshold : I.minBonds ≤ (bondCount I.sequence f : ℤ) := by
    simpa only [RecordsAccept, hf] using hacc
  apply (verify_correct (I, encodeRecords rs)).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [decodedLabels_encodeRecords]
    exact hv.1.symm
  · rw [stream_encodeRecords]
    exact (geometryValid_records_iff rs).mpr (injective_of_validRecords I.sequence rs hv)
  · rw [stream_encodeRecords, recordFold_bondCountRecords I.sequence rs f hf]
    exact hthreshold

theorem verify_complete (I : HPInstance) (hI : I.Accepts) :
    ∃ w : List Bool, w.length ≤
      (Polynomial.C 4 * Polynomial.X : Polynomial ℕ).eval (hpEncoding.encode I).length ∧
      verify (I, w) = true := by
  obtain ⟨rs, hlen, hacc⟩ := (hp_records_certificate_iff I).mp hI
  exact ⟨encodeRecords rs, encoded_records_bound I rs hlen, verify_encodeRecords I rs hacc⟩

/-- Packaging the actual assembled verifier. The only remaining parameter is
the concrete geometric machine data; soundness and completeness are proved
unconditionally above, and the word certificate bound is four times input size. -/
theorem hpStringFold_inNP_of_geometry
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record)) geometryEncoding geometryData) :
    InNP hpEncoding HPInstance.Accepts :=
  inNP_of_word_verifier HPInstance.Accepts (Polynomial.C 4 * Polynomial.X)
    (fun x => verify x = true) (verify_polyTimeDecidable hGeometry) verify_sound verify_complete

end ProteinFolding.CubicHPVerifier
