import ProteinFolding.Cubic.Proofs.PackingWordComputableHalf
import ProteinFolding.Cubic.Proofs.PackingWordSource
import ProteinFolding.Cubic.Proofs.VerifierPerfectArithmetic

/-! Actual polynomial-time generation of the frame's word stages. Unary
parameters are consumed by the explicit arithmetic, repetition and word
concatenation machines; output-size estimates alone are never used as a
substitute for an execution-time proof. -/

namespace ProteinFolding.CubicPacking.WordGenerator

open Computability Turing TM2CompositionPoly TM2ProductMap

variable {X : Type} {ex : FinEncoding X}

theorem repeatWord_eq_machine (u : Sequence) (n : ℕ) :
    repeatWord u n = TM2WordRepeat.wordRepeat u n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatWord, TM2WordRepeat.repeat_succ_prepend, ih]

noncomputable def natConstant (ex : FinEncoding X) (n : ℕ) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun _ => n) :=
  TM2Constants.constantComputable ex unaryFinEncodingNat n

noncomputable def wordConstant (ex : FinEncoding X) (u : Sequence) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun _ => u) :=
  TM2Constants.constantComputable ex sequenceEncoding u

noncomputable def add {f g : X → ℕ}
    (hf : TM2ComputableInPolyTime ex unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x + g x) :=
  compose (pairComputable hf hg) PerfectVerifierArithmetic.unaryAddComputable

noncomputable def mul {f g : X → ℕ}
    (hf : TM2ComputableInPolyTime ex unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x * g x) :=
  compose (pairComputable hf hg) PerfectUnaryMultiplication.unaryMulComputable

noncomputable def concat {f g : X → Sequence}
    (hf : TM2ComputableInPolyTime ex sequenceEncoding f)
    (hg : TM2ComputableInPolyTime ex sequenceEncoding g) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun x => f x ++ g x) :=
  compose (pairComputable hf hg) (TM2PairProjections.concatComputable Residue)

noncomputable def repeatSequence {f : X → Sequence} {g : X → ℕ}
    (hf : TM2ComputableInPolyTime ex sequenceEncoding f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun x => repeatWord (f x) (g x)) := by
  let h := compose (pairComputable hf hg) (TM2WordRepeat.computable Residue)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun x => by
        simpa only [Function.comp_apply, repeatWord_eq_machine] using h.outputsFun x }

noncomputable def repeatFixed (u : Sequence) :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding (repeatWord u) :=
  repeatSequence (wordConstant unaryFinEncodingNat u) (idComputableInPolyTime unaryFinEncodingNat)

noncomputable def edgeComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding edgeWord :=
  repeatFixed [.P, .H, .P]

noncomputable def faceComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding faceWord :=
  compose UnaryHalf.computable (repeatFixed [.P, .H, .H, .P])

theorem repeat_singleton (r : Residue) (n : ℕ) : repeatWord [r] n = List.replicate n r := by
  induction n <;> simp [repeatWord, List.replicate_succ, *]

noncomputable def residuePower (r : Residue) :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding (fun n => List.replicate n r) := by
  let h := repeatFixed [r]
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by simpa only [repeat_singleton] using h.outputsFun n }

def dimensionEncoding : FinEncoding (ℕ × ℕ) := pairEncoding unaryFinEncodingNat unaryFinEncodingNat

noncomputable def qComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => p.1) := TM2PairProjections.fstComputable _ _

noncomputable def QComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => p.2) := TM2PairProjections.sndComputable _ _

noncomputable def alphaComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => alpha p.2) := mul (natConstant dimensionEncoding 2) QComputable

noncomputable def betaComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => beta p.2) :=
  add (mul (natConstant dimensionEncoding 4) QComputable) (natConstant dimensionEncoding 2)

noncomputable def depthComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => depth p.1 p.2) := mul qComputable betaComputable

noncomputable def sideComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => side p.1 p.2) := add depthComputable (natConstant dimensionEncoding 2)

noncomputable def wallUnitComputable : TM2ComputableInPolyTime dimensionEncoding sequenceEncoding
    (fun p : ℕ × ℕ => wallUnit p.1 p.2) :=
  let eAlpha := compose alphaComputable edgeComputable
  let fDepth := compose depthComputable faceComputable
  let eBeta := compose betaComputable edgeComputable
  concat (concat (concat (concat eAlpha fDepth) eBeta) fDepth) eAlpha

noncomputable def qPredecessorComputable : TM2ComputableInPolyTime dimensionEncoding unaryFinEncodingNat
    (fun p : ℕ × ℕ => p.1 - 1) := compose qComputable PerfectUnaryPredecessor.predecessorComputable

noncomputable def gapWordComputable : TM2ComputableInPolyTime dimensionEncoding sequenceEncoding
    (fun p : ℕ × ℕ => gapWord p.1 p.2) :=
  let eTwo := wordConstant dimensionEncoding (edgeWord 2)
  let pPadding := compose
    (add (mul (natConstant dimensionEncoding 2) alphaComputable) (natConstant dimensionEncoding 4))
    (residuePower .P)
  concat eTwo (repeatSequence (concat pPadding eTwo) qPredecessorComputable)

noncomputable def wallsComputable : TM2ComputableInPolyTime dimensionEncoding sequenceEncoding
    (fun p : ℕ × ℕ => walls p.1 p.2) :=
  let pPadding := compose (mul (natConstant dimensionEncoding 2) alphaComputable) (residuePower .P)
  let repeated := repeatSequence (concat wallUnitComputable pPadding) qPredecessorComputable
  concat (concat repeated wallUnitComputable) gapWordComputable

noncomputable def subtractTwo : TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat
    (fun n : ℕ => n - 2) := by
  let h := compose PerfectUnaryPredecessor.predecessorComputable
    PerfectUnaryPredecessor.predecessorComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by simpa only [Function.comp_apply, Nat.sub_sub] using h.outputsFun n }

noncomputable def prefixWordComputable : TM2ComputableInPolyTime dimensionEncoding sequenceEncoding
    (fun p : ℕ × ℕ => prefixWord p.1 p.2) :=
  let dSquare := compose depthComputable CubicCertificates.unarySquareComputable
  let dCube := compose depthComputable PerfectVerifierArithmetic.unaryCubeComputable
  let eLong := compose
    (add (mul (natConstant dimensionEncoding 9) depthComputable) (natConstant dimensionEncoding 8))
    edgeComputable
  let fSquare := compose dSquare faceComputable
  let eDepth := compose depthComputable edgeComputable
  let pFour := wordConstant dimensionEncoding (List.replicate 4 .P)
  let pDPlusNine := compose (add depthComputable (natConstant dimensionEncoding 9)) (residuePower .P)
  let repeated := repeatSequence (concat fSquare pDPlusNine) (natConstant dimensionEncoding 3)
  let fSquareMinusTwo := compose (compose dSquare subtractTwo) faceComputable
  let pOne := wordConstant dimensionEncoding [.P]
  let hBulk := compose (add dCube (natConstant dimensionEncoding 2)) (residuePower .H)
  let pEnd := compose (add alphaComputable (natConstant dimensionEncoding 8)) (residuePower .P)
  concat (concat (concat (concat (concat (concat (concat (concat eLong fSquare) eDepth)
    pFour) repeated) fSquareMinusTwo) pOne) hBulk) pEnd

/-- The whole fixed frame, including its variable number of wall units. Item
blocks are generated separately from the source's terminated unary item word. -/
noncomputable def fixedFrameComputable : TM2ComputableInPolyTime dimensionEncoding sequenceEncoding
    (fun p : ℕ × ℕ => prefixWord p.1 p.2 ++ walls p.1 p.2) :=
  concat prefixWordComputable wallsComputable

end ProteinFolding.CubicPacking.WordGenerator
