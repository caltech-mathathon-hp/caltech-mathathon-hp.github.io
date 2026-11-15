import ProteinFolding.Tetrahedral.WordPieces
import ProteinFolding.Tetrahedral.FrameWordPHP
import ProteinFolding.Cubic.Proofs.PackingWordComputable
import ProteinFolding.Common.TM2WordInit
import ProteinFolding.Common.TM2UnarySubtraction

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

variable {X Y : Type} {ex : FinEncoding X} {ey : FinEncoding Y}

noncomputable def changeFunction {f g : X → Y} (h : TM2ComputableInPolyTime ex ey f)
    (heq : ∀ x, f x = g x) : TM2ComputableInPolyTime ex ey g where
  toTM2ComputableAux := h.toTM2ComputableAux
  time := h.time
  outputsFun x := by rw [← heq x]; exact h.outputsFun x

noncomputable def natConstant (ex : FinEncoding X) (n : ℕ) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun _ => n) :=
  CubicPacking.WordGenerator.natConstant ex n

noncomputable def wordConstant (ex : FinEncoding X) (w : Sequence) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun _ => w) :=
  CubicPacking.WordGenerator.wordConstant ex w

noncomputable def add {f g : X → ℕ} (hf : TM2ComputableInPolyTime ex unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x + g x) :=
  CubicPacking.WordGenerator.add hf hg

noncomputable def mul {f g : X → ℕ} (hf : TM2ComputableInPolyTime ex unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x * g x) :=
  CubicPacking.WordGenerator.mul hf hg

noncomputable def sub {f g : X → ℕ} (hf : TM2ComputableInPolyTime ex unaryFinEncodingNat f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => f x - g x) :=
  compose (pairComputable hf hg) TM2UnarySubtraction.subtractionComputable

noncomputable def concat {f g : X → Sequence} (hf : TM2ComputableInPolyTime ex sequenceEncoding f)
    (hg : TM2ComputableInPolyTime ex sequenceEncoding g) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun x => f x ++ g x) :=
  CubicPacking.WordGenerator.concat hf hg

theorem repeatWord_eq_machine (w : Sequence) (n : ℕ) : repeatWord w n = TM2WordRepeat.wordRepeat w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatWord, TM2WordRepeat.repeat_succ_prepend, ih]

noncomputable def repeatSequence {f : X → Sequence} {g : X → ℕ}
    (hf : TM2ComputableInPolyTime ex sequenceEncoding f)
    (hg : TM2ComputableInPolyTime ex unaryFinEncodingNat g) :
    TM2ComputableInPolyTime ex sequenceEncoding (fun x => repeatWord (f x) (g x)) :=
  changeFunction (compose (pairComputable hf hg) (TM2WordRepeat.computable Residue))
    (fun x => (repeatWord_eq_machine (f x) (g x)).symm)

noncomputable def repeatFixed (w : Sequence) :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding (repeatWord w) :=
  repeatSequence (wordConstant unaryFinEncodingNat w) (idComputableInPolyTime unaryFinEncodingNat)

noncomputable def residuePower (r : Residue) :
    TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding (fun n => List.replicate n r) :=
  CubicPacking.WordGenerator.residuePower r

noncomputable def capComputable : TM2ComputableInPolyTime sequenceEncoding sequenceEncoding capWord :=
  changeFunction (concat (concat (wordConstant sequenceEncoding [.P]) (idComputableInPolyTime sequenceEncoding))
    (wordConstant sequenceEncoding [.P])) (fun w => by simp [capWord])

theorem repeatWord_succ_append (w : Sequence) (n : ℕ) : repeatWord w (n + 1) = repeatWord w n ++ w := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simpa only [repeatWord, List.append_assoc] using congrArg (w ++ ·) ih

theorem dimerChain_eq_dropLast (q : ℕ) :
    dimerChain q = ((repeatWord [.H, .H, .P, .P, .P] q).dropLast.dropLast.dropLast) := by
  cases q with
  | zero => rfl
  | succ q => rw [repeatWord_succ_append]; simp [dimerChain]

/-- An actual TM2 emits the exact literal dimer word, including q=0. The
three terminal P symbols of a repeated five-letter block are removed by
three checked linear drop-last machines. -/
noncomputable def dimerComputable : TM2ComputableInPolyTime unaryFinEncodingNat sequenceEncoding dimerChain :=
  changeFunction (compose (compose (compose (repeatFixed [.H, .H, .P, .P, .P])
    (TM2WordInit.computable Residue)) (TM2WordInit.computable Residue)) (TM2WordInit.computable Residue))
    (fun q => (dimerChain_eq_dropLast q).symm)

end ProteinFolding.Tetrahedral.ReductionTM2
