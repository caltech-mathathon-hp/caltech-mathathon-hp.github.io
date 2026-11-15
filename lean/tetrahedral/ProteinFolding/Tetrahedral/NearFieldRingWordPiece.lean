import ProteinFolding.Tetrahedral.NearFieldRingBulkClearance

/-! The capped ring in the common ordered unit interface. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringTerminalSite_inB (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 3) (e : Fin 2) :
    InBSublattice (ringTerminalSite m F i e).val := by
  fin_cases e
  · exact (octEdgeZigzag_odd (by omega : 1 ≤ m) (ringSideFrame F i) 0).1
  · change InBSublattice (octEdgeZigzag m (ringSideFrame F i) (2 * m - 5)).val
    rw [ringSide_last_eq_reverse_three m hm]
    exact (octEdgeZigzag_odd (by omega : 1 ≤ m) (bulkReverseEdgeFrame (ringSideFrame F i)) 1).1

noncomputable def ringWordPiece (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) : PositionedWord where
  word := capWord (dimerChain (3 * (m - 2)))
  fold := cappedRingFold m hm heven F C D hC hD
  length_pos := by simp [capWord]
  first := C.seed
  last := D.seed
  first_eq := cappedRingFold_first m hm heven F C D hC hD
  last_eq := cappedRingFold_last m hm heven F C D hC hD

theorem ringWordPiece_hSupport_subset (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1) :
    hSupport (ringWordPiece m hm heven F C D hC hD).word
      (ringWordPiece m hm heven F C D hC hD).fold ⊆ octahedron m :=
  cappedRingFold_hSupport_subset_oct m hm heven F C D hC hD

theorem ringWordPiece_mem_solid_one (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (ringWordPiece m hm heven F C D hC hD).word.length) :
    (ringWordPiece m hm heven F C D hC hD).fold.pos i ∈ skinSolid m 1 :=
  cappedRingFold_mem_solid_one m hm heven F C D hC hD i

end ProteinFolding.Tetrahedral.NearField
