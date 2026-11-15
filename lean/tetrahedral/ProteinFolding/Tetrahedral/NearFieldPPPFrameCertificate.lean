import ProteinFolding.Tetrahedral.NearFieldPPPFrameData

/-! Uniform literal-list certificates for dangling sites and dangling ports. -/

namespace ProteinFolding.Tetrahedral

theorem nearFrame_dangling_index_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 0 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 0 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 0 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 1 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 1 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_kind2 (m q : ℕ)
    (r : Fin (nearFrameLength 2)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 2)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 2 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 2 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 2 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_kind3 (m q : ℕ)
    (r : Fin (nearFrameLength 3)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 3)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 3 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 3 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 3 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 4 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 4 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 4 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_kind5 (m q : ℕ)
    (r : Fin (nearFrameLength 5)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 5)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q 5 r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q 5 r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength 5 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_dangling_index_certificate (m q : ℕ) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameCoordinates m q kind r.val) i ∧
      tetraCoordinate m (nearFrameCoordinates m q kind r.val) i ≤ octRadius m + 3) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength kind := by
  fin_cases kind
  · exact nearFrame_dangling_index_kind0 m q r hr0 hrlast hb
  · exact nearFrame_dangling_index_kind1 m q r hr0 hrlast hb
  · exact nearFrame_dangling_index_kind2 m q r hr0 hrlast hb
  · exact nearFrame_dangling_index_kind3 m q r hr0 hrlast hb
  · exact nearFrame_dangling_index_kind4 m q r hr0 hrlast hb
  · exact nearFrame_dangling_index_kind5 m q r hr0 hrlast hb

theorem nearFrame_single_port_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 0 r.val d) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 0 r.val d) i ≤ octRadius m + 3) :
    d = nearFrameSinglePort 0 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 1 r.val d) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 1 r.val d) i ≤ octRadius m + 3) :
    d = nearFrameSinglePort 1 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind4_dir0 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 0) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 0) i ≤ octRadius m + 3) :
    0 = nearFrameSinglePort 4 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind4_dir1 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 1) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 1) i ≤ octRadius m + 3) :
    1 = nearFrameSinglePort 4 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind4_dir2 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 2) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 2) i ≤ octRadius m + 3) :
    2 = nearFrameSinglePort 4 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind4_dir3 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 3) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val 3) i ≤ octRadius m + 3) :
    3 = nearFrameSinglePort 4 r.val := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameStepCoordinates, nearFrameSinglePort, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength, nearFrameIsA,
    tetraCoordinate, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 ⊢
  all_goals omega

theorem nearFrame_single_port_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val d) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q 4 r.val d) i ≤ octRadius m + 3) :
    d = nearFrameSinglePort 4 r.val := by
  fin_cases d
  · exact nearFrame_single_port_kind4_dir0 m q r hr0 hrlast hb
  · exact nearFrame_single_port_kind4_dir1 m q r hr0 hrlast hb
  · exact nearFrame_single_port_kind4_dir2 m q r hr0 hrlast hb
  · exact nearFrame_single_port_kind4_dir3 m q r hr0 hrlast hb

end ProteinFolding.Tetrahedral

