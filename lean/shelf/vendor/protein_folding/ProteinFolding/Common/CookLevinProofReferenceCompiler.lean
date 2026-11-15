import ProteinFolding.Common.CookLevinProofAddressCompiler
import ProteinFolding.Common.CookLevinProofRowIndex

/-! Total natural-position versions of the arithmetic row references, with
actual polynomial TM2 implementations. On bounded positions these are exactly
the references of the unchanged typed tableau row. -/

namespace ProteinFolding.SAT.CookLevinReferenceCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinArithmeticCompiler
  CookLevinAddressCompiler CookLevinRowIndex CookLevinRows CookLevinAlphabet
  CookLevinWindow CookLevinCells CookLevinPaddedWindow

noncomputable def affineCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (blockBase stride offset : ℕ) (M t n : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat
      (fun x => t x * (base tm + M x * slope tm) + (blockBase + (n x * stride + offset))) := by
  let hc := pairComputable (pairComputable hM ht)
    (pairComputable hn (TM2Constants.constantComputable ex unaryFinEncodingNat offset))
  exact compose hc (addressComputable (base tm) (slope tm) blockBase stride)

noncomputable def controlRef (tm : FinTM2) (M t : ℕ) (c : Control tm) : ℕ :=
  t * (base tm + M * slope tm) + (controlIndex tm c).val

noncomputable def windowRef (tm : FinTM2) (M t : ℕ) (w : PaddedWindow tm) : ℕ :=
  t * (base tm + M * slope tm) + (controlCount tm + (windowIndex tm w).val)

noncomputable def replacementRef (tm : FinTM2) (M t : ℕ) (r : Replacement tm) : ℕ :=
  t * (base tm + M * slope tm) +
    (controlCount tm + windowCount tm + (replacementIndex tm r).val)

noncomputable def cellRef (tm : FinTM2) (M t n : ℕ) (k : tm.K)
    (b : Option (Symbol tm k)) : ℕ :=
  t * (base tm + M * slope tm) + (base tm + (n * slope tm + (cellIndex tm ⟨k, b⟩).val))

noncomputable def queryRef (tm : FinTM2) (M t n : ℕ) (k : tm.K)
    (q : CellWindow tm k) : ℕ :=
  t * (base tm + M * slope tm) +
    (base tm + (n * slope tm + (cellCount tm + (queryIndex tm ⟨k, q⟩).val)))

theorem controlRef_eq (tm : FinTM2) (M t : ℕ) (c : Control tm) :
    controlRef tm M t c = arithmeticReference tm M t (controlTag tm M c) := by
  rw [arithmeticReference_control]
  rfl

theorem windowRef_eq (tm : FinTM2) (M t : ℕ) (w : PaddedWindow tm) :
    windowRef tm M t w = arithmeticReference tm M t (windowTag tm M w) := by
  rw [arithmeticReference_window]
  simp only [windowRef, Nat.add_assoc]

theorem replacementRef_eq (tm : FinTM2) (M t : ℕ) (r : Replacement tm) :
    replacementRef tm M t r = arithmeticReference tm M t (replacementTag tm M r) := by
  rw [arithmeticReference_replacement]
  simp only [replacementRef, Nat.add_assoc]

theorem cellRef_eq (tm : FinTM2) (M t : ℕ) (n : Fin M) (k : tm.K)
    (b : Option (Symbol tm k)) :
    cellRef tm M t n.val k b = arithmeticReference tm M t (cellTag tm M k n b) := by
  rw [arithmeticReference_cell]
  simp only [cellRef, Nat.add_assoc]

theorem queryRef_eq (tm : FinTM2) (M t : ℕ) (n : Fin M) (k : tm.K)
    (q : CellWindow tm k) :
    queryRef tm M t n.val k q = arithmeticReference tm M t (queryTag tm M k n q) := by
  rw [arithmeticReference_query]
  simp only [queryRef, Nat.add_assoc]

noncomputable def controlRefCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (c : Control tm)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => controlRef tm (M x) (t x) c) := by
  simpa only [controlRef, Nat.mul_zero, Nat.zero_add] using affineCompiler tm 0 0
    (controlIndex tm c).val M t (fun _ => 0) hM ht
    (TM2Constants.constantComputable ex unaryFinEncodingNat 0)

noncomputable def windowRefCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (w : PaddedWindow tm)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => windowRef tm (M x) (t x) w) := by
  simpa only [windowRef, Nat.mul_zero, Nat.zero_add] using affineCompiler tm
    (controlCount tm) 0 (windowIndex tm w).val M t (fun _ => 0) hM ht
    (TM2Constants.constantComputable ex unaryFinEncodingNat 0)

noncomputable def replacementRefCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (r : Replacement tm)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat
      (fun x => replacementRef tm (M x) (t x) r) := by
  simpa only [replacementRef, Nat.mul_zero, Nat.zero_add] using affineCompiler tm
    (controlCount tm + windowCount tm) 0 (replacementIndex tm r).val M t (fun _ => 0) hM ht
    (TM2Constants.constantComputable ex unaryFinEncodingNat 0)

noncomputable def cellRefCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t n : X → ℕ) (k : tm.K) (b : Option (Symbol tm k))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => cellRef tm (M x) (t x) (n x) k b) :=
  affineCompiler tm (base tm) (slope tm) (cellIndex tm ⟨k, b⟩).val M t n hM ht hn

noncomputable def queryRefCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t n : X → ℕ) (k : tm.K) (q : CellWindow tm k)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => queryRef tm (M x) (t x) (n x) k q) :=
  affineCompiler tm (base tm) (slope tm) (cellCount tm + (queryIndex tm ⟨k, q⟩).val) M t n hM ht hn

end ProteinFolding.SAT.CookLevinReferenceCompiler
