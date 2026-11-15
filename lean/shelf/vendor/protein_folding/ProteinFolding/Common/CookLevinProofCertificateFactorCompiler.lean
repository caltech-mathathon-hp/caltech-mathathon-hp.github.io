import ProteinFolding.Common.CookLevinProofBoundaryCompiler
import ProteinFolding.Common.CookLevinProofRelationCompiler

/-! Actual polynomial TM2 generation of all variable-certificate alphabet
and no-hole factors. Their truth tables have fixed finite arity; only the
arithmetic positions and the two bounded loop indices grow with the input. -/

namespace ProteinFolding.SAT.CookLevinCertificateFactorCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinCircuit CookLevinLocal
open CookLevinAlphabet CookLevinRows CookLevinStepCNF CookLevinCertificateCNF
open CookLevinBoundaryCompiler CookLevinReferenceCompiler CookLevinRelationCompiler
open CookLevinRangeCNFCompiler CookLevinAddressCompiler CookLevinFactorThree
open CookLevinRowRename CookLevinRowIndex CookLevinCertificatePoints

noncomputable def cellRefs (tm : FinTM2) (M t n : ℕ) (k : tm.K) : List ℕ :=
  Finset.univ.toList.map (cellRef tm M t n k)

noncomputable def alphabetCNF {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H i : ℕ) : CNF :=
  relationCNF (cellRefs tm M 0 (H + i) tm.k₀)
    (unaryAllowed (fun v => v = none ∨ ∃ c, v = some (e c)))

noncomputable def alphabetCNFCompiler {X C : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H i : X → ℕ) (e : C → Symbol tm tm.k₀)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat i) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => alphabetCNF tm (M x) e (H x) (i x)) := by
  exact relationCNFListCompiler Finset.univ.toList
    (unaryAllowed (fun v => v = none ∨ ∃ c, v = some (e c)))
    (fun b x => cellRef tm (M x) 0 (H x + i x) tm.k₀ b)
    (fun b => cellRefCompiler tm M (fun _ => 0) (fun x => H x + i x) tm.k₀ b hM
      (TM2Constants.constantComputable ex unaryFinEncodingNat 0) (addMaps hH hi))

noncomputable def noHoleCNF (tm : FinTM2) (M H i j : ℕ) : CNF :=
  relationCNF (cellRefs tm M 0 (H + i) tm.k₀ ++ cellRefs tm M 0 (H + j) tm.k₀)
    (binaryAllowed (fun u v : Option (Symbol tm tm.k₀) => u = none → v = none))

noncomputable def noHoleSlots (tm : FinTM2) :
    List (Option (Symbol tm tm.k₀) ⊕ Option (Symbol tm tm.k₀)) :=
  Finset.univ.toList.map Sum.inl ++ Finset.univ.toList.map Sum.inr

noncomputable def noHoleIndex (tm : FinTM2) (M H i j : ℕ) :
    Option (Symbol tm tm.k₀) ⊕ Option (Symbol tm tm.k₀) → ℕ :=
  Sum.elim (cellRef tm M 0 (H + i) tm.k₀) (cellRef tm M 0 (H + j) tm.k₀)

theorem noHoleIndex_slots (tm : FinTM2) (M H i j : ℕ) :
    (noHoleSlots tm).map (noHoleIndex tm M H i j) =
      cellRefs tm M 0 (H + i) tm.k₀ ++ cellRefs tm M 0 (H + j) tm.k₀ := by
  simp only [noHoleSlots, noHoleIndex, List.map_append, List.map_map,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, cellRefs]

noncomputable def noHoleCNFCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H i j : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat i)
    (hj : TM2ComputableInPolyTime ex unaryFinEncodingNat j) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => noHoleCNF tm (M x) (H x) (i x) (j x)) := by
  let hindex : ∀ d, TM2ComputableInPolyTime ex unaryFinEncodingNat
      (fun x => noHoleIndex tm (M x) (H x) (i x) (j x) d) := by
    intro d
    cases d with
    | inl b =>
      exact cellRefCompiler tm M (fun _ => 0) (fun x => H x + i x) tm.k₀ b hM
        (TM2Constants.constantComputable ex unaryFinEncodingNat 0) (addMaps hH hi)
    | inr b =>
      exact cellRefCompiler tm M (fun _ => 0) (fun x => H x + j x) tm.k₀ b hM
        (TM2Constants.constantComputable ex unaryFinEncodingNat 0) (addMaps hH hj)
  let hc := relationCNFListCompiler (noHoleSlots tm)
    (binaryAllowed (fun u v : Option (Symbol tm tm.k₀) => u = none → v = none))
    (fun d x => noHoleIndex tm (M x) (H x) (i x) (j x) d) hindex
  simpa only [noHoleIndex_slots, noHoleCNF] using hc

noncomputable def alphabetFactorsCNF {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) : CNF :=
  (List.range B).flatMap (alphabetCNF tm M e H)

noncomputable def alphabetFactorsCompiler {X C : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H B : X → ℕ) (e : C → Symbol tm tm.k₀)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => alphabetFactorsCNF tm (M x) e (H x) (B x)) := by
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let hi := TM2PairProjections.sndComputable ex unaryFinEncodingNat
  let hc := alphabetCNFCompiler tm (fun p : X × ℕ => M p.1) (fun p : X × ℕ => H p.1)
    Prod.snd e (compose hfst hM) (compose hfst hH) hi
  exact rangeCNFCompiler B (fun p : X × ℕ => alphabetCNF tm (M p.1) e (H p.1) p.2) hB hc

noncomputable def noHoleFactorsCNF (tm : FinTM2) (M H B : ℕ) : CNF :=
  (List.range B).flatMap (fun i => (List.range B).flatMap (fun j =>
    if decide (i < j) then noHoleCNF tm M H i j else []))

noncomputable def guardedNoHoleCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H i j : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hi : TM2ComputableInPolyTime ex unaryFinEncodingNat i)
    (hj : TM2ComputableInPolyTime ex unaryFinEncodingNat j) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x =>
      if decide (i x < j x) then noHoleCNF tm (M x) (H x) (i x) (j x) else []) :=
  TM2Conditional.iteComputable (compose (pairComputable hi hj) TM2UnaryComparison.ltComputable)
    (noHoleCNFCompiler tm M H i j hM hH hi hj) (TM2Constants.constantComputable ex cnfEncoding [])

noncomputable def noHoleFactorsCompiler {X : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H B : X → ℕ)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => noHoleFactorsCNF tm (M x) (H x) (B x)) := by
  let ep := pairEncoding ex unaryFinEncodingNat
  let hfst := TM2PairProjections.fstComputable ex unaryFinEncodingNat
  let hfirst := TM2PairProjections.fstComputable ep unaryFinEncodingNat
  let hi := compose hfirst (TM2PairProjections.sndComputable ex unaryFinEncodingNat)
  let hj := TM2PairProjections.sndComputable ep unaryFinEncodingNat
  let hX := compose hfirst hfst
  let hc := guardedNoHoleCompiler tm
    (fun p : (X × ℕ) × ℕ => M p.1.1) (fun p : (X × ℕ) × ℕ => H p.1.1)
    (fun p : (X × ℕ) × ℕ => p.1.2) (fun p : (X × ℕ) × ℕ => p.2)
    (compose hX hM) (compose hX hH) hi hj
  let inner := rangeCNFCompiler (fun p : X × ℕ => B p.1)
    (fun p : (X × ℕ) × ℕ => if decide (p.1.2 < p.2)
      then noHoleCNF tm (M p.1.1) (H p.1.1) p.1.2 p.2 else []) (compose hfst hB) hc
  exact rangeCNFCompiler B (fun p : X × ℕ => (List.range (B p.1)).flatMap (fun j =>
    if decide (p.2 < j) then noHoleCNF tm (M p.1) (H p.1) p.2 j else [])) hB inner

noncomputable def certificateFactorsCNF {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) : CNF :=
  alphabetFactorsCNF tm M e H B ++ noHoleFactorsCNF tm M H B

noncomputable def certificateFactorsCompiler {X C : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M H B : X → ℕ) (e : C → Symbol tm tm.k₀)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hH : TM2ComputableInPolyTime ex unaryFinEncodingNat H)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => certificateFactorsCNF tm (M x) e (H x) (B x)) :=
  appendCompiler (alphabetFactorsCompiler tm M H B e hM hH hB) (noHoleFactorsCompiler tm M H B hM hH hB)

theorem cellRefs_eq (tm : FinTM2) (M t : ℕ) (n : Fin M) (k : tm.K) :
    cellRefs tm M t n.val k =
      (codeRefs tm M t (cellTag tm M k n)).map (renameIndex tm M) := by
  simp only [cellRefs, codeRefs, codeSlots, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun b _ => (cellRef_eq tm M t n k b).trans
    (renameIndex_reference tm M t (cellTag tm M k n b)).symm)

theorem rename_alphabetFactor {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) (i : Fin B) :
    renameCNF (renameIndex tm M)
      (relationCNF (alphabetFactor tm M e H B hM i).vars (alphabetFactor tm M e H B hM i).allowed) =
      alphabetCNF tm M e H i.val := by
  simp only [alphabetFactor, rename_relationCNF]
  rw [← cellRefs_eq]
  rfl

theorem rename_noHoleFactor (tm : FinTM2) (M H B : ℕ) (hM : H + B ≤ M) (i j : Fin B) :
    renameCNF (renameIndex tm M)
      (relationCNF (noHoleFactor tm M H B hM i j).vars (noHoleFactor tm M H B hM i j).allowed) =
      noHoleCNF tm M H i.val j.val := by
  simp only [noHoleFactor, rename_relationCNF, List.map_append]
  rw [← cellRefs_eq, ← cellRefs_eq]
  rfl

theorem alphabetFactorsCNF_eq {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) :
    alphabetFactorsCNF tm M e H B = renameCNF (renameIndex tm M)
      (compileConstraints ((List.finRange B).map (alphabetFactor tm M e H B hM))) := by
  rw [compileConstraints, List.flatMap_map, renameCNF_flatMap, alphabetFactorsCNF, range_flatMap_finRange]
  exact List.flatMap_congr (fun i _ => (rename_alphabetFactor tm M e H B hM i).symm)

theorem noHoleFactorsCNF_eq (tm : FinTM2) (M H B : ℕ) (hM : H + B ≤ M) :
    noHoleFactorsCNF tm M H B = renameCNF (renameIndex tm M)
      (compileConstraints ((List.finRange B).flatMap (fun i =>
        ((List.finRange B).filter (fun j => i < j)).map (noHoleFactor tm M H B hM i)))) := by
  simp only [compileConstraints, List.flatMap_assoc, List.flatMap_map, renameCNF_flatMap,
    noHoleFactorsCNF, range_flatMap_finRange]
  apply List.flatMap_congr
  intro i _
  rw [flatMap_filter_eq]
  apply List.flatMap_congr
  intro j _
  by_cases hij : i.val < j.val
  · simp only [Fin.lt_def, hij, decide_true, ↓reduceIte]
    exact (rename_noHoleFactor tm M H B hM i j).symm
  · simp only [Fin.lt_def, hij, decide_false, ↓reduceIte]
    rfl

theorem certificateFactorsCNF_eq {C : Type} (tm : FinTM2) (M : ℕ)
    (e : C → Symbol tm tm.k₀) (H B : ℕ) (hM : H + B ≤ M) :
    certificateFactorsCNF tm M e H B = renameCNF (renameIndex tm M)
      (compileConstraints (certificateFactors tm M e H B hM)) := by
  simp only [certificateFactorsCNF, certificateFactors, compileConstraints, List.flatMap_append,
    renameCNF_append]
  exact congrArg₂ (· ++ ·) (alphabetFactorsCNF_eq tm M e H B hM) (noHoleFactorsCNF_eq tm M H B hM)

noncomputable def certificateCNFCompiler {X C : Type} {ex : FinEncoding X} (tm : FinTM2)
    (M B : X → ℕ) (header : X → List (Symbol tm tm.k₀)) (e : C → Symbol tm tm.k₀)
    (bound : ∀ x, (header x).length + B x ≤ M x)
    (hM : TM2ComputableInPolyTime ex unaryFinEncodingNat M)
    (hB : TM2ComputableInPolyTime ex unaryFinEncodingNat B)
    (hh : TM2ComputableInPolyTime ex (wordEncoding (Symbol tm tm.k₀)) header) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => renameCNF (renameIndex tm (M x))
      (certificateCNF tm (M x) e (header x) (B x) (bound x))) := by
  let hlen := compose hh (CookLevinArithmeticCompiler.lengthComputable (wordEncoding (Symbol tm tm.k₀)))
  let hp := certificatePinsCompiler tm M B header hM hB hh
  let hf := certificateFactorsCompiler tm M (fun x => (header x).length) B e hM hlen hB
  let hc := appendCompiler hp hf
  have he : (fun x => certificatePins tm (M x) (header x) (B x) ++
      certificateFactorsCNF tm (M x) e (header x).length (B x)) =
      (fun x => renameCNF (renameIndex tm (M x)) (certificateCNF tm (M x) e (header x) (B x) (bound x))) := by
    funext x
    rw [certificateCNF, renameCNF_append, certificatePins_eq tm (M x) e (header x) (B x) (bound x),
      certificateFactorsCNF_eq tm (M x) e (header x).length (B x) (bound x)]
  rw [← he]
  exact hc

end ProteinFolding.SAT.CookLevinCertificateFactorCompiler
