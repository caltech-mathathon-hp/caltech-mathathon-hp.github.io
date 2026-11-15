import ProteinFolding.Tetrahedral.NearFieldDimerChainArithmetic
import ProteinFolding.Tetrahedral.OctahedralTrackGeometry

/-! Source-independent colours of the canonical endpoint sites. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeZigzag_inA_of_even {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (hr : r % 2 = 0) :
    InASublattice (octEdgeZigzag m F r).val := by
  have he : r = 2 * (r / 2) := by omega
  rw [he]
  exact (octEdgeZigzag_even hm F _).1

theorem edgeZigzag_inB_of_odd {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (hr : r % 2 = 1) :
    InBSublattice (octEdgeZigzag m F r).val := by
  have he : r = 2 * (r / 2) + 1 := by omega
  rw [he]
  exact (octEdgeZigzag_odd hm F _).1

theorem initialTerminal_inB (p : ConstructionParameters) :
    InBSublattice (octEdgeZigzag p.side entryEdgeFrame (2 * p.side - 3)).val := by
  apply edgeZigzag_inB_of_odd (by have h := p.side_ge; omega)
  have hm := p.side_ge
  omega

theorem frameFirstH_inA (p : ConstructionParameters) :
    InASublattice (octEdgeZigzag p.side entryEdgeFrame 0).val :=
  (octEdgeZigzag_even (by have h := p.side_ge; omega) entryEdgeFrame 0).1

theorem frameLastH_inA (p : ConstructionParameters) :
    InASublattice (octEdgeZigzag p.side exitEdgeFrame 0).val :=
  (octEdgeZigzag_even (by have h := p.side_ge; omega) exitEdgeFrame 0).1

theorem leftFillerFirstH_inA (p : ConstructionParameters) :
    InASublattice (octEdgeZigzag p.side entryEdgeFrame 2).val :=
  (octEdgeZigzag_even (by have h := p.side_ge; omega) entryEdgeFrame 1).1

theorem leftFillerLastH_inA (p : ConstructionParameters) :
    InASublattice (octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)).val := by
  apply edgeZigzag_inA_of_even (by have h := p.side_ge; omega)
  have h := p.leftFiller_ge
  omega

theorem rightFillerFirstH_inA (p : ConstructionParameters) :
    InASublattice (octEdgeZigzag p.side trackEdgeFrame (2 * (p.separatorIndex p.bins + 2))).val :=
  (octEdgeZigzag_even (by have h := p.side_ge; omega) trackEdgeFrame _).1

theorem rightFillerLastH_inB (p : ConstructionParameters) :
    InBSublattice (octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3)).val := by
  apply edgeZigzag_inB_of_odd (by have h := p.side_ge; omega)
  have hm := p.side_ge
  omega

theorem ringFirstH_inB {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) :
    InBSublattice (octEdgeZigzag m F 1).val := (octEdgeZigzag_odd hm F 0).1

theorem ringLastH_inB {m : ℕ} (hm : 3 ≤ m) (F : OctEdgeFrame) :
    InBSublattice (octEdgeZigzag m F (2 * m - 5)).val := by
  apply edgeZigzag_inB_of_odd (by omega)
  omega

theorem dimerLast_even_of_even_length (a q : ℕ) (hq : (q + 1) % 2 = 0) :
    dimerHIndex (2 * a) false q 1 % 2 = 0 := by
  dsimp [dimerHIndex, dimerFlip]
  omega

theorem dimerLast_odd_of_odd_length (a q : ℕ) (hq : (q + 1) % 2 = 1) :
    dimerHIndex (2 * a) false q 1 % 2 = 1 := by
  dsimp [dimerHIndex, dimerFlip]
  omega

end ProteinFolding.Tetrahedral.NearField
