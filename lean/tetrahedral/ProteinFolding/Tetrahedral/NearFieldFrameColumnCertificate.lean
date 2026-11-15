import ProteinFolding.Tetrahedral.NearFieldFrameColumnData

/-! Coordinate certificates show that a column met by a frame P-link has an edge owner. -/

namespace ProteinFolding.Tetrahedral

theorem nearFrameColumn_first_A_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 0 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false true d)
        (nearFrameColumnOtherFace 0 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 1 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false true d)
        (nearFrameColumnOtherFace 1 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_kind2 (m q : ℕ)
    (r : Fin (nearFrameLength 2)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 2)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 2 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false true d)
        (nearFrameColumnOtherFace 2 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_kind3 (m q : ℕ)
    (r : Fin (nearFrameLength 3)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 3)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 3 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false true d)
        (nearFrameColumnOtherFace 3 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 4 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false true d)
        (nearFrameColumnOtherFace 4 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_kind5 (m q : ℕ)
    (r : Fin (nearFrameLength 5)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 5)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace 5 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false true d)
        (nearFrameColumnOtherFace 5 false d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_A_certificate (m q : ℕ) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false true d) d = octRadius m) :
    nearFrameColumnOtherFace kind false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false true d)
        (nearFrameColumnOtherFace kind false d) = -octRadius m := by
  fin_cases kind
  · exact nearFrameColumn_first_A_kind0 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_A_kind1 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_A_kind2 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_A_kind3 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_A_kind4 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_A_kind5 m q r d hr0 hrlast hb hd

theorem nearFrameColumn_first_B_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 0 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val false false d)
        (nearFrameColumnOtherFace 0 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 1 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val false false d)
        (nearFrameColumnOtherFace 1 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_kind2 (m q : ℕ)
    (r : Fin (nearFrameLength 2)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 2)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 2 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val false false d)
        (nearFrameColumnOtherFace 2 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_kind3 (m q : ℕ)
    (r : Fin (nearFrameLength 3)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 3)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 3 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val false false d)
        (nearFrameColumnOtherFace 3 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val false false d)
        (nearFrameColumnOtherFace 4 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_kind5 (m q : ℕ)
    (r : Fin (nearFrameLength 5)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 5)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 5 false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val false false d)
        (nearFrameColumnOtherFace 5 false d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_first_B_certificate (m q : ℕ) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace kind false d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val false false d)
        (nearFrameColumnOtherFace kind false d) = octRadius m - 1 := by
  fin_cases kind
  · exact nearFrameColumn_first_B_kind0 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_B_kind1 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_B_kind2 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_B_kind3 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_B_kind4 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_first_B_kind5 m q r d hr0 hrlast hb hd

theorem nearFrameColumn_second_A_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 0 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true true d)
        (nearFrameColumnOtherFace 0 true d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 1 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true true d)
        (nearFrameColumnOtherFace 1 true d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind2 (m q : ℕ)
    (r : Fin (nearFrameLength 2)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 2)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 2 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true true d)
        (nearFrameColumnOtherFace 2 true d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind3 (m q : ℕ)
    (r : Fin (nearFrameLength 3)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 3)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 3 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true true d)
        (nearFrameColumnOtherFace 3 true d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind4_dir0 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 0) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 0) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 0) 0 = octRadius m) :
    nearFrameColumnOtherFace 4 true 0 ≠ 0 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 0)
        (nearFrameColumnOtherFace 4 true 0) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind4_dir1 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 1) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 1) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 1) 1 = octRadius m) :
    nearFrameColumnOtherFace 4 true 1 ≠ 1 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 1)
        (nearFrameColumnOtherFace 4 true 1) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind4_dir2 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 2) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 2) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 2) 2 = octRadius m) :
    nearFrameColumnOtherFace 4 true 2 ≠ 2 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 2)
        (nearFrameColumnOtherFace 4 true 2) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind4_dir3 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 3) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 3) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 3) 3 = octRadius m) :
    nearFrameColumnOtherFace 4 true 3 ≠ 3 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true 3)
        (nearFrameColumnOtherFace 4 true 3) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 4 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true true d)
        (nearFrameColumnOtherFace 4 true d) = -octRadius m := by
  fin_cases d
  · exact nearFrameColumn_second_A_kind4_dir0 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind4_dir1 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind4_dir2 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind4_dir3 m q r hr0 hrlast hb hd

theorem nearFrameColumn_second_A_kind5 (m q : ℕ)
    (r : Fin (nearFrameLength 5)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 5)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace 5 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true true d)
        (nearFrameColumnOtherFace 5 true d) = -octRadius m := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_A_certificate (m q : ℕ) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hb : ∀ i, -octRadius m ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true true d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true true d) i ≤ octRadius m)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true true d) d = octRadius m) :
    nearFrameColumnOtherFace kind true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true true d)
        (nearFrameColumnOtherFace kind true d) = -octRadius m := by
  fin_cases kind
  · exact nearFrameColumn_second_A_kind0 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind1 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind2 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind3 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind4 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_A_kind5 m q r d hr0 hrlast hb hd

theorem nearFrameColumn_second_B_kind0 (m q : ℕ)
    (r : Fin (nearFrameLength 0)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 0)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 0 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 0 r.val true false d)
        (nearFrameColumnOtherFace 0 true d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind1 (m q : ℕ)
    (r : Fin (nearFrameLength 1)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 1)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 1 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 1 r.val true false d)
        (nearFrameColumnOtherFace 1 true d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind2 (m q : ℕ)
    (r : Fin (nearFrameLength 2)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 2)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 2 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 2 r.val true false d)
        (nearFrameColumnOtherFace 2 true d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind3 (m q : ℕ)
    (r : Fin (nearFrameLength 3)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 3)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 3 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 3 r.val true false d)
        (nearFrameColumnOtherFace 3 true d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind4_dir0 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 0) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 0) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 0) 0 = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 true 0 ≠ 0 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 0)
        (nearFrameColumnOtherFace 4 true 0) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind4_dir1 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 1) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 1) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 1) 1 = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 true 1 ≠ 1 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 1)
        (nearFrameColumnOtherFace 4 true 1) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind4_dir2 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 2) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 2) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 2) 2 = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 true 2 ≠ 2 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 2)
        (nearFrameColumnOtherFace 4 true 2) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind4_dir3 (m q : ℕ)
    (r : Fin (nearFrameLength 4))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 3) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 3) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 3) 3 = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 true 3 ≠ 3 ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false 3)
        (nearFrameColumnOtherFace 4 true 3) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_kind4 (m q : ℕ)
    (r : Fin (nearFrameLength 4)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 4)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 4 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 4 r.val true false d)
        (nearFrameColumnOtherFace 4 true d) = octRadius m - 1 := by
  fin_cases d
  · exact nearFrameColumn_second_B_kind4_dir0 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind4_dir1 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind4_dir2 m q r hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind4_dir3 m q r hr0 hrlast hb hd

theorem nearFrameColumn_second_B_kind5 (m q : ℕ)
    (r : Fin (nearFrameLength 5)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength 5)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace 5 true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q 5 r.val true false d)
        (nearFrameColumnOtherFace 5 true d) = octRadius m - 1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases d <;> fin_cases r
  all_goals dsimp [nearFrameColumnOwnerCoordinates, nearFrameColumnOtherFace, nearFrameCoordinates,
    nearFrameReference, nearFrameOffset, nearFrameOffsetTriple, nearFrameLength,
    tetraCoordinate, columnOpposite, bondComponent, octRadius] at hr0 hrlast h0 h1 h2 h3 hd ⊢
  all_goals omega

theorem nearFrameColumn_second_B_certificate (m q : ℕ) (kind : Fin 6)
    (r : Fin (nearFrameLength kind)) (d : Fin 4)
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hb : ∀ i, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true false d) i ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true false d) i ≤ octRadius m - 1)
    (hd : tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true false d) d = -(2 * (m : ℤ) - 1)) :
    nearFrameColumnOtherFace kind true d ≠ d ∧
      tetraCoordinate m (nearFrameColumnOwnerCoordinates m q kind r.val true false d)
        (nearFrameColumnOtherFace kind true d) = octRadius m - 1 := by
  fin_cases kind
  · exact nearFrameColumn_second_B_kind0 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind1 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind2 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind3 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind4 m q r d hr0 hrlast hb hd
  · exact nearFrameColumn_second_B_kind5 m q r d hr0 hrlast hb hd

end ProteinFolding.Tetrahedral

