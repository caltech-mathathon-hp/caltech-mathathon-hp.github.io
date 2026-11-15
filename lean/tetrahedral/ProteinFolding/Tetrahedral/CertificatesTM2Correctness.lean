import ProteinFolding.Tetrahedral.CertificatesTM2ScoreSemantics
import ProteinFolding.Tetrahedral.CertificatesTM2Verifier

/-! The concrete polynomial-time machine decides the frozen direction
certificate predicate. This discharges NP membership without a machine-level
hypothesis and leaves NP-hardness as the separate remaining complexity task. -/

namespace ProteinFolding.Tetrahedral

open CertificatesTM2Records CertificatesTM2Pairs CertificatesTM2Semantics

theorem directionPosition_consecutive (S : Sequence) (ds : DirectionWord)
    (i j : Fin S.length) (hij : i.val + 1 = j.val) :
    tetrahedralLattice.Adj (directionPosition S ds i) (directionPosition S ds j) := by
  change tetrahedralLattice.Adj (walkPosition ds i.val) (walkPosition ds j.val)
  rw [← hij, walkPosition]
  exact step_adj _ _

theorem validDirectionWord_iff_length_injective (S : Sequence) (ds : DirectionWord) :
    ValidDirectionWord S ds ↔
      ds.length = S.length ∧ Function.Injective (directionPosition S ds) := by
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, directionPosition_consecutive S ds⟩

theorem geometryValid_directions_iff (S : Sequence) (ds : DirectionWord) :
    geometryValid ((recordsOfDirections S ds).map some) = true ↔
      Function.Injective (directionPosition S ds) := by
  rw [geometryValid_records_iff]
  have hlen := recordsOfDirections_length S ds
  constructor
  · intro h i j heq
    let ir : Fin (recordsOfDirections S ds).length := ⟨i.val, by omega⟩
    let jr : Fin (recordsOfDirections S ds).length := ⟨j.val, by omega⟩
    have hpos : recordPosition (recordsOfDirections S ds) ir.val =
        recordPosition (recordsOfDirections S ds) jr.val := by
      dsimp [ir, jr]
      rw [recordPosition_eq_walk S ds i.val i.isLt,
        recordPosition_eq_walk S ds j.val j.isLt]
      exact heq
    have he := congrArg (fun k : Fin (recordsOfDirections S ds).length => k.val) (h hpos)
    exact Fin.ext he
  · intro h i j heq
    let si : Fin S.length := ⟨i.val, by omega⟩
    let sj : Fin S.length := ⟨j.val, by omega⟩
    have hpos : directionPosition S ds si = directionPosition S ds sj := by
      change walkPosition ds i.val = walkPosition ds j.val
      rw [← recordPosition_eq_walk S ds i.val (by have := si.isLt; exact this),
        ← recordPosition_eq_walk S ds j.val (by have := sj.isLt; exact this)]
      exact heq
    have he := congrArg (fun k : Fin S.length => k.val) (h hpos)
    exact Fin.ext he

theorem certificateFold_bondCountRecords (S : Sequence) (ds : DirectionWord)
    (f : Fold tetrahedralLattice S.length) (hf : certificateFold S ds = some f) :
    bondCountRecords ((recordsOfDirections S ds).map some) = bondCount S f := by
  unfold certificateFold at hf
  split at hf
  · cases Option.some.inj hf
    apply bondCountRecords_eq_bondCount S _ (recordsOfDirections_labels S ds)
    intro i
    exact (recordPosition_eq_walk S ds i.val i.isLt).symm
  · cases hf

theorem directionAccepts_records_iff (I : HPInstance) (ds : DirectionWord) :
    DirectionAccepts (I, ds) ↔ ds.length = I.sequence.length ∧
      geometryValid ((recordsOfDirections I.sequence ds).map some) = true ∧
      I.minBonds ≤ (bondCountRecords ((recordsOfDirections I.sequence ds).map some) : ℤ) := by
  by_cases hv : ValidDirectionWord I.sequence ds
  · let f : Fold tetrahedralLattice I.sequence.length :=
      ⟨directionPosition I.sequence ds, hv.2.1, hv.2.2⟩
    have hf : certificateFold I.sequence ds = some f := by simp [certificateFold, hv, f]
    have hscore := certificateFold_bondCountRecords I.sequence ds f hf
    have hgeo := (geometryValid_directions_iff I.sequence ds).2 hv.2.1
    simp only [DirectionAccepts, hf, hv.1, hgeo, hscore, true_and]
  · have hnot : ¬(ds.length = I.sequence.length ∧
        geometryValid ((recordsOfDirections I.sequence ds).map some) = true) := by
      rw [geometryValid_directions_iff, ← validDirectionWord_iff_length_injective]
      exact hv
    simp only [DirectionAccepts, certificateFold, dif_neg hv]
    tauto

theorem geometryValid_false_of_none (input : List (Option CertificatesTM2Records.Record))
    (hnone : none ∈ input) : geometryValid input = false := by
  cases h : geometryValid input
  · rfl
  · obtain ⟨rs, hrs⟩ := geometryValid_some input h
    rw [hrs] at hnone
    simp at hnone

theorem tetrahedralVerifier_correct (x : HPInstance × DirectionWord) :
    CertificatesTM2Verifier.verify x = true ↔ DirectionAccepts x := by
  obtain ⟨I, ds⟩ := x
  by_cases hlen : I.sequence.length = ds.length
  · have hz := CertificatesTM2Zip.zipRecords_eq_recordsOfDirections I.sequence ds hlen
    rw [CertificatesTM2Verifier.verify, CertificatesTM2Verifier.records, hz]
    rw [Bool.and_eq_true, decide_eq_true_eq, directionAccepts_records_iff]
    simp only [hlen, true_and]
  · have hn := (CertificatesTM2Zip.none_mem_zipRecords_iff 0 I.sequence ds).2 hlen
    have hb := geometryValid_false_of_none _ hn
    rw [CertificatesTM2Verifier.verify, CertificatesTM2Verifier.records, hb]
    simp only [Bool.false_and, Bool.false_eq_true, directionAccepts_records_iff]
    have hlen' : ds.length ≠ I.sequence.length := Ne.symm hlen
    simp [hlen']

theorem hpVerifierPolyTime : HPVerifierPolyTime := by
  refine ⟨CertificatesTM2Verifier.verify, ⟨CertificatesTM2Verifier.verifyComputable⟩, ?_⟩
  exact tetrahedralVerifier_correct

/-- HP folding on the fixed diamond lattice belongs to NP under the frozen
word/signed-threshold encoding and the actual mathlib TM2 model. -/
theorem hp_inNP : InNP hpEncoding HPInstance.Accepts :=
  hp_inNP_of_verifier_polyTime hpVerifierPolyTime

end ProteinFolding.Tetrahedral
