import ProteinFolding.Tetrahedral.FrameForcingItemIndices
import ProteinFolding.Tetrahedral.SeparatorArithmetic

/-! A declared chain fitting a perturbed bin, after the three small
anchor/separator sizes are excluded, must be an input item chain. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem ConstructionParameters.ring_exceeds_bin_window (p : ConstructionParameters) :
    p.binDimers + p.sigma + 6 < 3 * (p.side - 2) := by
  have hside := p.side_eq_track
  have hleft : p.leftFiller = p.binDimers + p.scale := rfl
  have hscale : p.scale = p.sigma + 8 := rfl
  omega

theorem ReductionChainTag.is_item_of_bin_size (p : ConstructionParameters) (items : List ℕ)
    (tag : ReductionChainTag) (q : ℕ) (h : ReductionChainTag.Admissible p items tag q)
    (hne₁ : q ≠ 1) (hne₂ : q ≠ 2) (hne₃ : q ≠ 3)
    (hbound : q ≤ p.binDimers + p.sigma + 6) : tag.isItem = true := by
  have hsize := h.1
  have hfiller := p.fillers_exceed_bin_window q hbound
  have hring := p.ring_exceeds_bin_window
  cases tag with
  | entry k => exact False.elim (hne₁ hsize)
  | separator k => exact False.elim (hne₂ hsize)
  | exit k => exact False.elim (hne₃ hsize)
  | leftFiller => change q = p.leftFiller at hsize; omega
  | rightFiller => change q = p.rightFiller at hsize; omega
  | item s => rfl
  | ring r => change q = 3 * (p.side - 2) at hsize; omega

theorem ReductionDimerProvenance.chain_is_item_of_bin_size (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (i : (catalogue p items bulkLengths gaps hbulk).val.Index)
    (hne₁ : (catalogue p items bulkLengths gaps hbulk).val.q i ≠ 1)
    (hne₂ : (catalogue p items bulkLengths gaps hbulk).val.q i ≠ 2)
    (hne₃ : (catalogue p items bulkLengths gaps hbulk).val.q i ≠ 3)
    (hbound : (catalogue p items bulkLengths gaps hbulk).val.q i ≤ p.binDimers + p.sigma + 6) :
    ((catalogue p items bulkLengths gaps hbulk).val.tag i).isItem = true := by
  let c := (catalogue p items bulkLengths gaps hbulk).val
  change c.q i ≠ 1 at hne₁
  change c.q i ≠ 2 at hne₂
  change c.q i ≠ 3 at hne₃
  change c.q i ≤ p.binDimers + p.sigma + 6 at hbound
  change (c.tag i).isItem = true
  exact ReductionChainTag.is_item_of_bin_size p items (c.tag i) (c.q i)
    ((catalogue p items bulkLengths gaps hbulk).property i) hne₁ hne₂ hne₃ hbound

end ProteinFolding.Tetrahedral
