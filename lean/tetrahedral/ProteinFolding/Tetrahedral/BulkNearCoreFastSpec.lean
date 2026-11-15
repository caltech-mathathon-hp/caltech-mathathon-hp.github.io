import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsReference

/-! A cheaper decidable presentation of the original core escape check.
The final theorem derives the unchanged public predicate by logical equivalence. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def BulkNearReferenceRowFast (i : Fin 234) : Prop :=
  ∃ p ∈ bulkNearSegmentPoints i, bulkZ p = 0 ∧ bulkFastDamaged 50 p

instance (i : Fin 234) : Decidable (BulkNearReferenceRowFast i) := by
  unfold BulkNearReferenceRowFast
  infer_instance

theorem bulkNearReferenceRowFast_iff (i : Fin 234) :
    BulkNearReferenceRowFast i ↔ BulkNearReferenceRow i := by
  unfold BulkNearReferenceRowFast BulkNearReferenceRow bulkNearSegmentSupport
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, hz, hd⟩
    exact ⟨p, hp, hd, hz⟩
  · rintro ⟨p, hp, hd, hz⟩
    exact ⟨p, hp, hz, hd⟩

def bulkNearReferencePotentialFast (i : Fin 234) : BulkSegmentOrder :=
  let x := bulkNearCoordinateMin i + bulkNearCoordinateMax i
  if BulkNearReferenceRowFast i then toLex (2, toLex (|x|, 0))
  else if 0 < bulkAlpha 50 (bulkNearSegmentRoot i) then
    toLex (1, toLex (bulkAlpha 50 (bulkNearSegmentRoot i), x))
  else toLex (0, toLex (x, 0))

theorem bulkNearReferencePotentialFast_eq (i : Fin 234) :
    bulkNearReferencePotentialFast i = bulkNearReferencePotential i := by
  unfold bulkNearReferencePotentialFast bulkNearReferencePotential
  rw [bulkNearReferenceXhat_coordinates i]
  simp only [bulkNearReferenceRowFast_iff]

def BulkNearCoreFastCheck (i : Fin 234) : Prop :=
  bulkNearSegmentCore i = true →
    if (bulkNearCoreCase i).val = 0 then
      bulkNearCoreSource i ∈ bulkNearSegmentPoints i ∧
        (bulkFastCoverDirections 50 (bulkNearCoreSource i)).card ≤ 1
    else if (bulkNearCoreCase i).val = 1 then
      bulkNearCoreSource i ∈ bulkNearSegmentPoints i ∧
        bulkNearCoreTarget i ∈ bulkNearSegmentPoints (bulkNearCoreNext i) ∧
        bulkFastCoverBond 50 (bulkNearCoreSource i) (bulkNearCoreTarget i) ∧
        bulkNearSegmentVertex (bulkNearCoreNext i) = bulkNearSegmentVertex i ∧
        bulkNearReferencePotentialFast i < bulkNearReferencePotentialFast (bulkNearCoreNext i)
    else bulkNearEscapeStart (bulkNearCoreException i) ∈ bulkNearSegmentPoints i ∧
      bulkNearEscapeVertex (bulkNearCoreException i) = bulkNearSegmentVertex i

instance (i : Fin 234) : Decidable (BulkNearCoreFastCheck i) := by
  unfold BulkNearCoreFastCheck
  infer_instance

theorem bulkNearCoreFastCheck_sound (i : Fin 234) (h : BulkNearCoreFastCheck i) :
    BulkNearCoreEscapeCheck i := by
  intro hcore
  have hc := h hcore
  by_cases h0 : (bulkNearCoreCase i).val = 0
  · rw [if_pos h0] at hc ⊢
    exact ⟨List.mem_toFinset.mpr hc.1, hc.2⟩
  · rw [if_neg h0] at hc ⊢
    by_cases h1 : (bulkNearCoreCase i).val = 1
    · rw [if_pos h1] at hc ⊢
      obtain ⟨hp, hq, hb, hv, hlt⟩ := hc
      exact ⟨List.mem_toFinset.mpr hp, List.mem_toFinset.mpr hq, hb, hv,
        by simpa only [bulkNearReferencePotentialFast_eq] using hlt⟩
    · rw [if_neg h1] at hc ⊢
      exact ⟨List.mem_toFinset.mpr hc.1, hc.2⟩

end ProteinFolding.Tetrahedral
