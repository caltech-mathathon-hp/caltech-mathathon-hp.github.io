import ProteinFolding.Common.CookLevinProofRangeCNFCompiler
import ProteinFolding.Common.CookLevinProofReferenceCompiler
import ProteinFolding.Common.CookLevinProofWordLookup
import ProteinFolding.Common.CookLevinProofCertificateCNF
import ProteinFolding.Common.TM2UnaryComparison
import ProteinFolding.Common.CookLevinProofFactorThree
import ProteinFolding.Common.CookLevinProofRowRename

/-! Actual finite TM2 compilers for one-hot boundary pins. Dynamic header
letters are read from the encoded header word by the checked unary lookup
machine. All component enumerations are fixed finite types of the verifier. -/

namespace ProteinFolding.SAT.CookLevinBoundaryCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinCircuit
open CookLevinAlphabet CookLevinPaddedWindow CookLevinReferenceCompiler
open CookLevinRangeCNFCompiler CookLevinCNFCompiler CookLevinLiteralCompiler CookLevinWordLookup
open CookLevinArithmeticCompiler CookLevinAddressCompiler CookLevinFactorThree
open CookLevinRows CookLevinStepCNF CookLevinGlobalCNF CookLevinWindowCNF CookLevinRowIndex CookLevinRowRename

noncomputable def finitePins {D : Type} [Fintype D] (index : D → ℕ) (value : D → Bool) : CNF :=
  Finset.univ.toList.flatMap (fun d => [[⟨index d, value d⟩]])

theorem rename_componentPins {D : Type} [Fintype D] (tm : FinTM2) (M t : ℕ)
    (tag : D → Bit tm M) (v : D) :
    renameCNF (renameIndex tm M) (pins (componentPins tm M t tag v)) =
      finitePins (fun d => arithmeticReference tm M t (tag d)) (fun d => @decide (d = v) (Classical.propDecidable _)) := by
  classical
  simp only [componentPins, codeRefs, codeSlots, finiteCode, List.map_map, Function.comp_def,
    List.zip_map', pins, renameCNF, renameClause, List.map_map, List.map_cons, List.map_nil,
    renameLiteral, renameIndex_reference, finitePins, ← List.map_eq_flatMap]

theorem range_flatMap_finRange {D : Type} (n : ℕ) (f : ℕ → List D) :
    (List.range n).flatMap f = (List.finRange n).flatMap (fun i => f i.val) := by
  rw [← List.map_coe_finRange n, List.flatMap_map]

theorem flatMap_filter_eq {D E : Type} (xs : List D) (p : D → Bool) (f : D → List E) :
    (xs.filter p).flatMap f = xs.flatMap (fun x => if p x then f x else []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [List.flatMap_cons, h, ih]

theorem renameCNF_append (r : ℕ → ℕ) (φ ψ : CNF) :
    renameCNF r (φ ++ ψ) = renameCNF r φ ++ renameCNF r ψ := List.map_append

theorem renameCNF_flatMap {D : Type} (r : ℕ → ℕ) (xs : List D) (f : D → CNF) :
    renameCNF r (xs.flatMap f) = xs.flatMap (fun d => renameCNF r (f d)) := List.map_flatMap

theorem pins_append (xs ys : List (ℕ × Bool)) : pins (xs ++ ys) = pins xs ++ pins ys := List.map_append

theorem pins_flatMap {D : Type} (xs : List D) (f : D → List (ℕ × Bool)) :
    pins (xs.flatMap f) = xs.flatMap (fun d => pins (f d)) := List.map_flatMap

noncomputable def finitePinsCompiler {X D : Type} [Fintype D] {ex : FinEncoding X}
    (index : D → X → ℕ) (value : D → X → Bool)
    (hi : ∀ d, TM2ComputableInPolyTime ex unaryFinEncodingNat (index d))
    (hv : ∀ d, TM2ComputableInPolyTime ex finEncodingBoolBool (value d)) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => finitePins (fun d => index d x) (fun d => value d x)) :=
  fixedListCNFCompiler Finset.univ.toList (fun d x => [[⟨index d x, value d x⟩]])
    (fun d => compose (pairComputable (hi d) (hv d)) singletonCNFComputable)

noncomputable def controlPins (tm : FinTM2) (M t : ℕ) (v : Control tm) : CNF := by
  classical
  exact finitePins (controlRef tm M t) (fun c => decide (c = v))

theorem controlPins_eq (tm : FinTM2) (M t : ℕ) (v : Control tm) :
    controlPins tm M t v = renameCNF (renameIndex tm M)
      (pins (componentPins tm M t (controlTag tm M) v)) := by
  classical
  rw [rename_componentPins]
  simp only [controlPins, finitePins, controlRef_eq]

noncomputable def controlPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t : X → ℕ) (v : Control tm)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => controlPins tm (M x) (t x) v) := by
  classical
  exact finitePinsCompiler (fun c x => controlRef tm (M x) (t x) c) (fun c _ => decide (c = v))
    (fun c => controlRefCompiler tm M t c hM ht)
    (fun c => TM2Constants.constantComputable ex finEncodingBoolBool (decide (c = v)))

noncomputable def cellPins (tm : FinTM2) (M t n : ℕ) (k : tm.K)
    (v : Option (Symbol tm k)) : CNF := by
  classical
  exact finitePins (cellRef tm M t n k) (fun b => decide (b = v))

theorem cellPins_eq (tm : FinTM2) (M t : ℕ) (n : Fin M) (k : tm.K)
    (v : Option (Symbol tm k)) :
    cellPins tm M t n.val k v = renameCNF (renameIndex tm M)
      (pins (componentPins tm M t (cellTag tm M k n) v)) := by
  classical
  rw [rename_componentPins]
  simp only [cellPins, finitePins, cellRef_eq]
  congr 2
  funext d
  congr 3
  by_cases hd : d = v <;> simp [hd]

noncomputable def cellPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t n : X → ℕ) (k : tm.K) (v : Option (Symbol tm k))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => cellPins tm (M x) (t x) (n x) k v) := by
  classical
  exact finitePinsCompiler (fun b x => cellRef tm (M x) (t x) (n x) k b)
    (fun b _ => decide (b = v)) (fun b => cellRefCompiler tm M t n k b hM ht hn)
    (fun b => TM2Constants.constantComputable ex finEncodingBoolBool (decide (b = v)))

noncomputable def headerCellPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M t n : X → ℕ) (header : X → List (Symbol tm tm.k₀))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (ht : TM2ComputableInPolyTime ex unaryFinEncodingNat t)
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n)
    (hh : TM2ComputableInPolyTime ex (wordEncoding (Symbol tm tm.k₀)) header) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => cellPins tm (M x) (t x) (n x) tm.k₀ ((header x)[n x]?)) := by
  classical
  let hp : ∀ b : Option (Symbol tm tm.k₀),
      TM2ComputableInPolyTime ex finEncodingBoolBool (fun x => decide (b = (header x)[n x]?)) := by
    intro b
    let h := compose (pairComputable hh hn) (lookupTestComputable (Symbol tm tm.k₀) b)
    simpa only [Function.comp_def, lookupTest, eq_comm] using h
  exact finitePinsCompiler (fun b x => cellRef tm (M x) (t x) (n x) tm.k₀ b)
    (fun b x => decide (b = (header x)[n x]?))
    (fun b => cellRefCompiler tm M t n tm.k₀ b hM ht hn) hp

noncomputable def headerPins (tm : FinTM2) (M : ℕ) (header : List (Symbol tm tm.k₀)) : CNF :=
  (List.range header.length).flatMap (fun n => cellPins tm M 0 n tm.k₀ header[n]?)

noncomputable def headerPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M : X → ℕ) (header : X → List (Symbol tm tm.k₀))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hh : TM2ComputableInPolyTime ex (wordEncoding (Symbol tm tm.k₀)) header) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => headerPins tm (M x) (header x)) := by
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let hn := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  let hc := headerCellPinsCompiler tm (fun p : X × ℕ => M p.1) (fun _ => 0) Prod.snd
    (fun p : X × ℕ => header p.1) (compose hfst hM)
    (TM2Constants.constantComputable _ unaryFinEncodingNat 0) hn (compose hfst hh)
  let hlen := compose hh (lengthComputable (wordEncoding (Symbol tm tm.k₀)))
  exact rangeCNFCompiler (fun x => (header x).length)
    (fun p : X × ℕ => cellPins tm (M p.1) 0 p.2 tm.k₀ (header p.1)[p.2]?) hlen hc

noncomputable def suffixPins (tm : FinTM2) (M H B : ℕ) : CNF :=
  (List.range M).flatMap (fun n => if decide (H + B ≤ n) then cellPins tm M 0 n tm.k₀ none else [])

noncomputable def suffixPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H B : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => suffixPins tm (M x) (H x) (B x)) := by
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let hn := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  let hp := compose (pairComputable (addMaps (compose hfst hH) (compose hfst hB)) hn)
    TM2UnaryComparison.leComputable
  let hc := cellPinsCompiler tm (fun p : X × ℕ => M p.1) (fun _ => 0) Prod.snd tm.k₀ none
    (compose hfst hM) (TM2Constants.constantComputable _ unaryFinEncodingNat 0) hn
  let hg := TM2Conditional.iteComputable hp hc (TM2Constants.constantComputable _ cnfEncoding [])
  exact rangeCNFCompiler M (fun p : X × ℕ =>
    if decide (H p.1 + B p.1 ≤ p.2) then cellPins tm (M p.1) 0 p.2 tm.k₀ none else []) hM hg

noncomputable def blankStackPins (tm : FinTM2) (M : ℕ) (k : tm.K) : CNF :=
  (List.range M).flatMap (fun n => cellPins tm M 0 n k none)

noncomputable def blankStackPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M : X → ℕ) (k : tm.K) (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => blankStackPins tm (M x) k) := by
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let hn := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  let hc := cellPinsCompiler tm (fun p : X × ℕ => M p.1) (fun _ => 0) Prod.snd k none
    (compose hfst hM) (TM2Constants.constantComputable _ unaryFinEncodingNat 0) hn
  exact rangeCNFCompiler M (fun p : X × ℕ => cellPins tm (M p.1) 0 p.2 k none) hM hc

noncomputable def unusedStackPins (tm : FinTM2) (M : ℕ) : CNF := by
  classical
  letI := tm.kFin
  exact (Finset.univ.toList.filter (fun k => decide (k ≠ tm.k₀))).flatMap (blankStackPins tm M)

noncomputable def unusedStackPinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M : X → ℕ) (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => unusedStackPins tm (M x)) := by
  classical
  letI := tm.kFin
  exact fixedListCNFCompiler (Finset.univ.toList.filter (fun k => decide (k ≠ tm.k₀)))
    (fun k x => blankStackPins tm (M x) k) (fun k => blankStackPinsCompiler tm M k hM)

noncomputable def certificatePins (tm : FinTM2) (M : ℕ)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) : CNF :=
  controlPins tm M 0 (some tm.main, tm.initialState) ++ headerPins tm M header ++
    suffixPins tm M header.length B ++ unusedStackPins tm M

theorem headerPins_eq (tm : FinTM2) (M : ℕ)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) :
    headerPins tm M header = renameCNF (renameIndex tm M)
      (pins ((List.finRange header.length).flatMap (fun i => componentPins tm M 0
        (cellTag tm M tm.k₀ (CookLevinCertificatePoints.headerIndex header.length hM i))
          (some header[i.val])))) := by
  rw [pins_flatMap, renameCNF_flatMap, headerPins, range_flatMap_finRange]
  apply List.flatMap_congr
  intro i _
  rw [← cellPins_eq]
  simp only [CookLevinCertificatePoints.headerIndex, List.getElem?_eq_getElem i.isLt]

theorem suffixPins_eq (tm : FinTM2) (M H B : ℕ) :
    suffixPins tm M H B = renameCNF (renameIndex tm M)
      (pins (((List.finRange M).filter (fun i => decide (H + B ≤ i.val))).flatMap
        (fun i => componentPins tm M 0 (cellTag tm M tm.k₀ i) none))) := by
  rw [pins_flatMap, renameCNF_flatMap, flatMap_filter_eq, suffixPins, range_flatMap_finRange]
  apply List.flatMap_congr
  intro i _
  by_cases hi : H + B ≤ i.val
  · simp only [hi, decide_true, ↓reduceIte]
    exact cellPins_eq tm M 0 i tm.k₀ none
  · simp [hi]

theorem blankStackPins_eq (tm : FinTM2) (M : ℕ) (k : tm.K) :
    blankStackPins tm M k = renameCNF (renameIndex tm M)
      (pins ((List.finRange M).flatMap (fun n => componentPins tm M 0 (cellTag tm M k n) none))) := by
  rw [pins_flatMap, renameCNF_flatMap, blankStackPins, range_flatMap_finRange]
  exact List.flatMap_congr (fun n _ => cellPins_eq tm M 0 n k none)

theorem unusedStackPins_eq (tm : FinTM2) (M : ℕ) :
    unusedStackPins tm M = renameCNF (renameIndex tm M) (pins (by
      classical
      letI := tm.kFin
      exact (Finset.univ.toList.filter (fun k => decide (k ≠ tm.k₀))).flatMap (fun k =>
        (List.finRange M).flatMap (fun n => componentPins tm M 0 (cellTag tm M k n) none)))) := by
  classical
  letI := tm.kFin
  rw [pins_flatMap, renameCNF_flatMap]
  exact List.flatMap_congr (fun k _ => blankStackPins_eq tm M k)

theorem certificatePins_eq {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) :
    certificatePins tm M header B = renameCNF (renameIndex tm M)
      (pins (CookLevinCertificateCNF.certificateBindings tm M e header B hM)) := by
  classical
  letI := tm.kFin
  simp only [CookLevinCertificateCNF.certificateBindings, pins_append, renameCNF_append, certificatePins]
  rw [controlPins_eq, headerPins_eq tm M header B hM, suffixPins_eq, unusedStackPins_eq]

noncomputable def certificatePinsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M B : X → ℕ) (header : X → List (Symbol tm tm.k₀))
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B)
    (hh : TM2ComputableInPolyTime ex (wordEncoding (Symbol tm tm.k₀)) header) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => certificatePins tm (M x) (header x) (B x)) := by
  let hlen := compose hh (lengthComputable (wordEncoding (Symbol tm tm.k₀)))
  exact appendCompiler
    (appendCompiler
      (appendCompiler
        (controlPinsCompiler tm M (fun _ => 0) (some tm.main, tm.initialState) hM
          (TM2Constants.constantComputable ex unaryFinEncodingNat 0))
        (headerPinsCompiler tm M header hM hh))
      (suffixPinsCompiler tm M (fun x => (header x).length) B hM hlen hB))
    (unusedStackPinsCompiler tm M hM)

end ProteinFolding.SAT.CookLevinBoundaryCompiler
