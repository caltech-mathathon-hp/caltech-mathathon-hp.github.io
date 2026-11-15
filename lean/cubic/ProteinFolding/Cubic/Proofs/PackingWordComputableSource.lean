import ProteinFolding.Cubic.Proofs.PackingWordComputable
import ProteinFolding.Cubic.Proofs.PackingBalanceComputable
import ProteinFolding.Common.TM2WordInit
import ProteinFolding.Common.TM2UnaryToBinary
import ProteinFolding.Common.TM2WordTemplates

/-! Actual source-dependent stages of the normalized packing-frame generator.
All source numbers are read under the existing unary packing encoding; the
computed side is converted to the frozen target's canonical binary encoding.
The item word uses two variable templates and a prefix-delimited item code. -/

namespace ProteinFolding.CubicPacking.WordGenerator

open Computability Turing TM2CompositionPoly TM2ProductMap

noncomputable def sourceBinsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat sourceBins :=
  add Packing.binsComputable (natConstant Packing.instanceEncoding 1)

noncomputable def sourceQComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat sourceQ :=
  mul (add sourceBinsComputable (natConstant Packing.instanceEncoding 1)) Packing.capacityComputable

noncomputable def sourceScaleComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat sourceScale :=
  mul (natConstant Packing.instanceEncoding 4)
    (add sourceBinsComputable (natConstant Packing.instanceEncoding 1))

noncomputable def sourceDimensionsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding dimensionEncoding
      (fun I => (sourceBins I, sourceQ I)) := pairComputable sourceBinsComputable sourceQComputable

noncomputable def sourceSideComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat sourceSide :=
  compose (f := fun I => (sourceBins I, sourceQ I)) (g := fun p : ℕ × ℕ => side p.1 p.2)
    sourceDimensionsComputable sideComputable

noncomputable def sourceSideBinaryComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding finEncodingNatBool sourceSide :=
  compose (f := sourceSide) (g := id) sourceSideComputable TM2UnaryToBinary.unaryToBinaryComputable

noncomputable def sourceFixedFrameComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun I => prefixWord (sourceBins I) (sourceQ I) ++ walls (sourceBins I) (sourceQ I)) :=
  compose (f := fun I => (sourceBins I, sourceQ I))
    (g := fun p : ℕ × ℕ => prefixWord p.1 p.2 ++ walls p.1 p.2)
    sourceDimensionsComputable fixedFrameComputable

def sourceItemTemplate (I : Packing.Instance) : Sequence :=
  faceWord (depth (sourceBins I) (sourceQ I) * sourceScale I)

def sourceItemPadding (I : Packing.Instance) : Sequence := List.replicate (4 * sourceSide I) .P

noncomputable def sourceItemTemplateComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding sourceItemTemplate :=
  compose (f := fun I => depth (sourceBins I) (sourceQ I) * sourceScale I) (g := faceWord)
    (mul (compose (f := fun I => (sourceBins I, sourceQ I))
      (g := fun p : ℕ × ℕ => depth p.1 p.2) sourceDimensionsComputable depthComputable)
      sourceScaleComputable) faceComputable

noncomputable def sourceItemPaddingComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding sourceItemPadding :=
  compose (f := fun I => 4 * sourceSide I) (g := fun n => List.replicate n Residue.P)
    (mul (natConstant Packing.instanceEncoding 4) sourceSideComputable) (residuePower .P)

def paddedItemCode (I : Packing.Instance) : List Bool := Packing.itemEncoding.encode (I.capacity :: I.sizes)
def prefixItemCode (I : Packing.Instance) : List Bool := false :: (paddedItemCode I).dropLast

noncomputable def paddedItemCodeComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding (wordEncoding Bool) paddedItemCode := by
  let header := compose
    (pairComputable (Packing.toCode Packing.capacityComputable)
      (TM2Constants.constantComputable Packing.instanceEncoding (wordEncoding Bool) [false]))
    (TM2PairProjections.concatComputable Bool)
  let h := compose (pairComputable header (Packing.toCode Packing.sizesComputable))
    (TM2PairProjections.concatComputable Bool)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [paddedItemCode, Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons]
          using h.outputsFun I }

noncomputable def prefixItemCodeComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding (wordEncoding Bool) prefixItemCode :=
  compose
    (f := fun I => ([false], (paddedItemCode I).dropLast))
    (g := fun p : List Bool × List Bool => p.1 ++ p.2)
    (pairComputable
      (TM2Constants.constantComputable Packing.instanceEncoding (wordEncoding Bool) [false])
      (compose paddedItemCodeComputable (TM2WordInit.computable Bool)))
    (TM2PairProjections.concatComputable Bool)

def prefixItems (xs : List ℕ) : List Bool := xs.flatMap fun a => false :: unaryEncodeNat a

theorem prefixItems_append_false (xs : List ℕ) :
    prefixItems xs ++ [false] = false :: Packing.itemEncoding.encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [prefixItems, List.flatMap_cons, List.cons_append, List.append_assoc,
      Packing.itemEncoding, SAT.encTerminated] at *
    rw [ih]
    rfl

theorem prefixItemCode_eq (I : Packing.Instance) : prefixItemCode I = prefixItems (I.capacity :: I.sizes) := by
  have h := congrArg List.dropLast (prefixItems_append_false (I.capacity :: I.sizes))
  simp only [List.dropLast_concat] at h
  change prefixItems (I.capacity :: I.sizes) = (false :: paddedItemCode I).dropLast at h
  have hnon : paddedItemCode I ≠ [] := by
    intro he
    have hl := Packing.itemEncoding_length (I.capacity :: I.sizes)
    change (paddedItemCode I).length = _ at hl
    rw [he] at hl
    simp only [List.length_nil, List.length_cons, List.sum_cons] at hl
    omega
  rw [List.dropLast_cons_of_ne_nil hnon] at h
  exact h.symm

theorem repeatWord_add (u : Sequence) (m n : ℕ) :
    repeatWord u (m + n) = repeatWord u m ++ repeatWord u n := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih => simp [repeatWord, Nat.succ_add, ih, List.append_assoc]

theorem repeatWord_repeatWord (u : Sequence) (m n : ℕ) :
    repeatWord (repeatWord u m) n = repeatWord u (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeatWord, ih, ← repeatWord_add]
    congr 1
    ring

theorem faceWord_mul (t a : ℕ) (ht : 2 ∣ t) :
    faceWord (t * a) = repeatWord (faceWord t) a := by
  obtain ⟨k, rfl⟩ := ht
  have hd : (2 * k * a) / 2 = k * a := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  simp only [faceWord, hd, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact (repeatWord_repeatWord [.P, .H, .H, .P] k a).symm

theorem unary_flatMap_templates (u v : Sequence) (n : ℕ) :
    (unaryEncodeNat n).flatMap (fun b => if b then u else v) = repeatWord u n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, repeatWord, ih]

theorem itemWords_from_templates (q Q c : ℕ) (xs : List ℕ) :
    (prefixItems xs).flatMap
      (fun b => if b then faceWord (depth q Q * c) else List.replicate (4 * side q Q) .P) =
      itemWords q Q (xs.map (c * ·)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    dsimp only [prefixItems, itemWords] at ih
    simp only [prefixItems, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
      Bool.false_eq_true, if_false, unary_flatMap_templates, ih, List.map_cons,
      itemWords, List.flatMap_cons]
    rw [← faceWord_mul _ _ (Nat.dvd_mul_right_of_dvd (depth_even q Q) c)]
    simp only [Nat.mul_assoc]

theorem sourceItems_from_templates (I : Packing.Instance) :
    (prefixItemCode I).flatMap
      (fun b => if b then sourceItemTemplate I else sourceItemPadding I) =
      itemWords (sourceBins I) (sourceQ I) (sourceWidths I) := by
  rw [prefixItemCode_eq]
  exact itemWords_from_templates (sourceBins I) (sourceQ I) (sourceScale I) (I.capacity :: I.sizes)

/-- Every item occurrence is generated from its unary block, with its own
preceding connector. The two templates themselves are computed from the input. -/
noncomputable def sourceItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding
      (fun I => itemWords (sourceBins I) (sourceQ I) (sourceWidths I)) := by
  let h := compose
    (f := fun I => ((sourceItemTemplate I, sourceItemPadding I), prefixItemCode I))
    (g := TM2WordTemplates.substitute)
    (pairComputable (pairComputable sourceItemTemplateComputable sourceItemPaddingComputable)
      prefixItemCodeComputable)
    (TM2WordTemplates.computable Residue)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_apply, TM2WordTemplates.substitute, TM2WordTemplates.words,
          sourceItems_from_templates] using h.outputsFun I }

/-- The complete normalized reduction word is generated by an actual
polynomial-time finite TM2, including its item-dependent blocks and connectors. -/
noncomputable def sourceWordComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sequenceEncoding sourceWord :=
  concat sourceFixedFrameComputable sourceItemsComputable

/-- The unguarded body of the candidate reduction, with the target's existing
binary side encoding. The source side-condition guard is assembled separately. -/
noncomputable def unguardedInputComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding perfectEncoding
      (fun I => (sourceWord I, sourceSide I)) :=
  pairComputable sourceWordComputable sourceSideBinaryComputable

end ProteinFolding.CubicPacking.WordGenerator
