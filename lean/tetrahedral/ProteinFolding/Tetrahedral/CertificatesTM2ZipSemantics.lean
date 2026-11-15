import ProteinFolding.Tetrahedral.CertificatesTM2Zip

namespace ProteinFolding.Tetrahedral.CertificatesTM2Zip

theorem none_mem_zipRecords_iff (p : Fin 4) (S : Sequence) (ds : DirectionWord) :
    none ∈ zipRecords p S ds ↔ S.length ≠ ds.length := by
  induction S generalizing p ds with
  | nil =>
    cases ds <;> simp [zipRecords]
  | cons r S ih =>
    cases ds with
    | nil => simp [zipRecords]
    | cons d ds => simpa [zipRecords] using ih d ds

theorem zipRecords_getElem? (p : Fin 4) (S : Sequence) (ds : DirectionWord)
    (hlen : S.length = ds.length) (i : ℕ) :
    (zipRecords p S ds)[i]? =
      (S[i]?).map (fun r => some (r, if i = 0 then p else ds[i - 1]?.getD 0)) := by
  induction S generalizing p ds i with
  | nil =>
    have hds : ds = [] := List.length_eq_zero.mp hlen.symm
    subst ds
    simp [zipRecords]
  | cons r S ih =>
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      cases i with
      | zero => simp [zipRecords]
      | succ i =>
        simp only [zipRecords, List.getElem?_cons_succ]
        rw [ih d ds (by simpa using hlen)]
        cases i <;> simp

theorem zipRecords_eq_recordsOfDirections (S : Sequence) (ds : DirectionWord)
    (hlen : S.length = ds.length) :
    zipRecords 0 S ds = (CertificatesTM2Records.recordsOfDirections S ds).map some := by
  apply List.ext_getElem?
  intro i
  rw [zipRecords_getElem? 0 S ds hlen]
  by_cases hi : i < S.length
  · simp [CertificatesTM2Records.recordsOfDirections, hi]
  · simp [CertificatesTM2Records.recordsOfDirections, hi, List.getElem?_eq_none (by omega : S.length ≤ i)]

end ProteinFolding.Tetrahedral.CertificatesTM2Zip
