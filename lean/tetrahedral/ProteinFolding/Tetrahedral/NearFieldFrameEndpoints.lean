import ProteinFolding.Tetrahedral.NearFieldFramePaths

/-! The literal Appendix C paths join their prescribed frame H-sites. -/

namespace ProteinFolding.Tetrahedral

def nearFrameRouteFrame (kind : Fin 6) : OctEdgeFrame :=
  if kind = 0 ∨ kind = 1 ∨ kind = 2 then entryEdgeFrame else exitEdgeFrame

def nearFrameStartIndex (m q : ℕ) (kind : Fin 6) : ℕ :=
  if kind = 0 then 0 else if kind = 1 then q else if kind = 2 then 2 * m - 4
  else if kind = 3 then 2 * m - 2 else if kind = 4 then q + 7 else 2

def nearFrameEndIndex (m q : ℕ) (kind : Fin 6) : ℕ :=
  if kind = 0 then 3 else if kind = 1 then q + 3 else if kind = 2 then 2 * m - 2
  else if kind = 3 then 2 * m - 4 else if kind = 4 then q else 0

theorem nearFrame_start_eq (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    nearFramePoint m q kind hq ⟨0, by have h := nearFrameLength_ge_five kind; omega⟩ =
      octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameStartIndex m q kind) := by
  dsimp [octRadius] at hqhi
  have hm : 1 ≤ m := by omega
  apply Subtype.ext
  fin_cases kind <;> simp [nearFrameRouteFrame, Fin.ext_iff]
  all_goals first
    | (rw [entryEdgeZigzag_coordinates hm]
       funext k
       fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
         nearFrameOffset, nearFrameOffsetTriple, nearFrameStartIndex, entryEdgeCoordinates,
         nearFrameLength, octRadius] <;> omega)
    | (rw [exitEdgeZigzag_coordinates hm]
       funext k
       fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
         nearFrameOffset, nearFrameOffsetTriple, nearFrameStartIndex, exitEdgeCoordinates,
         nearFrameLength, octRadius] <;> omega)

theorem nearFrame_end_eq (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    nearFramePoint m q kind hq ⟨nearFrameLength kind - 1, by have h := nearFrameLength_ge_five kind; omega⟩ =
      octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameEndIndex m q kind) := by
  dsimp [octRadius] at hqhi
  have hm : 1 ≤ m := by omega
  apply Subtype.ext
  fin_cases kind <;> simp [nearFrameRouteFrame, Fin.ext_iff]
  all_goals first
    | (rw [entryEdgeZigzag_coordinates hm]
       funext k
       fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
         nearFrameOffset, nearFrameOffsetTriple, nearFrameEndIndex, entryEdgeCoordinates,
         nearFrameLength, octRadius] <;> omega)
    | (rw [exitEdgeZigzag_coordinates hm]
       funext k
       fin_cases k <;> dsimp [nearFramePoint, nearFrameCoordinates, nearFrameReference,
         nearFrameOffset, nearFrameOffsetTriple, nearFrameEndIndex, exitEdgeCoordinates,
         nearFrameLength, octRadius] <;> omega)

theorem nearFrame_endpoint_indices (m q : ℕ) (kind : Fin 6)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    nearFrameStartIndex m q kind < 2 * m - 1 ∧ nearFrameEndIndex m q kind < 2 * m - 1 := by
  fin_cases kind <;> dsimp [nearFrameStartIndex, nearFrameEndIndex, octRadius] at *
  all_goals constructor <;> omega

theorem nearFrame_endpoints_mem_oct (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    nearFramePoint m q kind hq ⟨0, by have h := nearFrameLength_ge_five kind; omega⟩ ∈ octahedron m ∧
      nearFramePoint m q kind hq ⟨nearFrameLength kind - 1,
        by have h := nearFrameLength_ge_five kind; omega⟩ ∈ octahedron m := by
  have hm : 1 ≤ m := by dsimp [octRadius] at hqhi; omega
  have hb := nearFrame_endpoint_indices m q kind hqlo hqhi
  rw [nearFrame_start_eq m q kind hq hqlo hqhi, nearFrame_end_eq m q kind hq hqlo hqhi]
  constructor
  · have h := octEdgeZigzag_mem hm (nearFrameRouteFrame kind) hb.1
    exact h.elim (fun h => h.1.1) (fun h => h.1.1)
  · have h := octEdgeZigzag_mem hm (nearFrameRouteFrame kind) hb.2
    exact h.elim (fun h => h.1.1) (fun h => h.1.1)

end ProteinFolding.Tetrahedral
