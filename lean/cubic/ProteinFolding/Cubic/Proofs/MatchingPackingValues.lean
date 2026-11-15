import ProteinFolding.Cubic.Proofs.PackingBalanceComputable
import ProteinFolding.Cubic.Proofs.VerifierPerfectArithmetic
import ProteinFolding.Common.NumericPacking
import ProteinFolding.Common.SAT.ThreeDimensionalMatching

/-! Actual polynomial-time unary arithmetic for the bounded numerical matching
gadget. Exponents are fixed constants of the construction. Each arithmetic
operation is composed from the already proved finite TM2 machines. -/

namespace ProteinFolding.MatchingPacking.Values

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections
open NumericPacking ThreeDimensionalMatching

section Arithmetic
variable {X : Type} {ex : FinEncoding X} {u v : X → ℕ}

noncomputable def constant (n : ℕ) : TM2ComputableInPolyTime ex unaryFinEncodingNat (fun _ : X => n) :=
  TM2Constants.constantComputable ex unaryFinEncodingNat n

noncomputable def add (hu : TM2ComputableInPolyTime ex unaryFinEncodingNat u)
    (hv : TM2ComputableInPolyTime ex unaryFinEncodingNat v) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => u x + v x) :=
  compose (pairComputable hu hv) PerfectVerifierArithmetic.unaryAddComputable

noncomputable def mul (hu : TM2ComputableInPolyTime ex unaryFinEncodingNat u)
    (hv : TM2ComputableInPolyTime ex unaryFinEncodingNat v) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => u x * v x) :=
  compose (pairComputable hu hv) PerfectUnaryMultiplication.unaryMulComputable

noncomputable def sub (hu : TM2ComputableInPolyTime ex unaryFinEncodingNat u)
    (hv : TM2ComputableInPolyTime ex unaryFinEncodingNat v) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => u x - v x) :=
  compose (pairComputable hu hv) TM2UnarySubtraction.subtractionComputable

/-- The exponent is a fixed parameter of the machine, rather than an input. -/
noncomputable def power (hu : TM2ComputableInPolyTime ex unaryFinEncodingNat u) :
    (k : ℕ) → TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => u x ^ k)
  | 0 => by simpa only [pow_zero] using (constant (ex := ex) 1)
  | k + 1 => by
    let h := mul (power hu k) hu
    exact
      { toTM2ComputableAux := h.toTM2ComputableAux
        time := h.time
        outputsFun := fun x => by simpa only [pow_succ] using h.outputsFun x }

end Arithmetic

noncomputable def baseComputable : TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat base := by
  let h := add (mul (constant 8) (idComputableInPolyTime unaryFinEncodingNat)) (constant 64)
  exact h

noncomputable def offsetComputable : TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat offset := by
  exact power baseComputable 6

section Digits
variable {X : Type} {ex : FinEncoding X} {n x y z s k : X → ℕ}

noncomputable def digitsComputable
    (hn : TM2ComputableInPolyTime ex unaryFinEncodingNat n)
    (hx : TM2ComputableInPolyTime ex unaryFinEncodingNat x)
    (hy : TM2ComputableInPolyTime ex unaryFinEncodingNat y)
    (hz : TM2ComputableInPolyTime ex unaryFinEncodingNat z)
    (hs : TM2ComputableInPolyTime ex unaryFinEncodingNat s)
    (hk : TM2ComputableInPolyTime ex unaryFinEncodingNat k) :
    TM2ComputableInPolyTime ex unaryFinEncodingNat
      (fun a => digits (base (n a)) (x a) (y a) (z a) (s a) (k a)) := by
  let hb := compose hn baseComputable
  let h := add hx (mul hb (add hy (mul hb (add hz (mul hb (add hs (mul hb hk)))))))
  exact h

end Digits

noncomputable def capacityComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat NumericPacking.capacity := by
  let hn := idComputableInPolyTime unaryFinEncodingNat
  let hd := digitsComputable hn hn hn hn (constant 3) (constant 15)
  exact add (mul (constant 4) offsetComputable) hd

def pairEncodingNat : FinEncoding (ℕ × ℕ) := pairEncoding unaryFinEncodingNat unaryFinEncodingNat

noncomputable def xComputable (real : Bool) :
    TM2ComputableInPolyTime pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => xToken ni.1 ni.2 real) := by
  let hn := fstComputable unaryFinEncodingNat unaryFinEncodingNat
  let hi := sndComputable unaryFinEncodingNat unaryFinEncodingNat
  let hd := digitsComputable hn (add hi (constant 1)) (constant 0) (constant 0)
    (constant (if real then 1 else 0)) (constant 1)
  exact add (compose (g := NumericPacking.offset) hn offsetComputable) hd

noncomputable def yComputable (real : Bool) :
    TM2ComputableInPolyTime pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => yToken ni.1 ni.2 real) := by
  let hn := fstComputable unaryFinEncodingNat unaryFinEncodingNat
  let hi := sndComputable unaryFinEncodingNat unaryFinEncodingNat
  let hd := digitsComputable hn (constant 0) (add hi (constant 1)) (constant 0)
    (constant (if real then 2 else 0)) (constant 2)
  exact add (compose (g := NumericPacking.offset) hn offsetComputable) hd

noncomputable def zComputable (real : Bool) :
    TM2ComputableInPolyTime pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => zToken ni.1 ni.2 real) := by
  let hn := fstComputable unaryFinEncodingNat unaryFinEncodingNat
  let hi := sndComputable unaryFinEncodingNat unaryFinEncodingNat
  let hd := digitsComputable hn (constant 0) (constant 0) (add hi (constant 1))
    (constant (if real then 0 else 3)) (constant 4)
  exact add (compose (g := NumericPacking.offset) hn offsetComputable) hd

def selectorEncoding : FinEncoding (ℕ × Triple) := pairEncoding unaryFinEncodingNat tripleFieldsEncoding

noncomputable def selectorComputable :
    TM2ComputableInPolyTime selectorEncoding unaryFinEncodingNat
      (fun nt : ℕ × Triple => selector nt.1 nt.2.1 nt.2.2.1 nt.2.2.2) := by
  let hn := fstComputable unaryFinEncodingNat tripleFieldsEncoding
  let ht := sndComputable unaryFinEncodingNat tripleFieldsEncoding
  let hi := compose ht (fstComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
  let hrest := compose ht (sndComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
  let hj := compose hrest (fstComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hk := compose hrest (sndComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hd := digitsComputable hn (sub hn (add hi (constant 1)))
    (sub hn (add hj (constant 1))) (sub hn (add hk (constant 1))) (constant 0) (constant 8)
  exact add (compose (g := NumericPacking.offset) hn offsetComputable) hd

noncomputable def itemWordComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat (wordEncoding Bool)
      (fun n => Packing.itemEncoding.encode [n]) := by
  let hcode := Packing.toCode (idComputableInPolyTime unaryFinEncodingNat)
  let hfalse := TM2Constants.constantComputable unaryFinEncodingNat (wordEncoding Bool) [false]
  let h := compose (pairComputable hcode hfalse) (concatComputable Bool)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [Function.comp_def, Packing.itemEncoding, SAT.encTerminated,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, unaryFinEncodingNat] using h.outputsFun n }

noncomputable def doubledItemComputable {X : Type} {ex : FinEncoding X} {v : X → ℕ}
    (hv : TM2ComputableInPolyTime ex unaryFinEncodingNat v) :
    TM2ComputableInPolyTime ex (wordEncoding Bool) (fun x => Packing.itemEncoding.encode [2 * v x]) :=
  compose (g := fun n => Packing.itemEncoding.encode [n]) (mul (constant 2) hv) itemWordComputable

end ProteinFolding.MatchingPacking.Values
