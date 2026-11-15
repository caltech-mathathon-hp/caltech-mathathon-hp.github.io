import ProteinFolding.Common.Statement
import Mathlib.Computability.Encoding

/-!
# Finite encodings

Shared word, pair, sequence, and signed-binary encodings for both dimensions.
All lengths below are actual word lengths over fixed finite alphabets.
-/

namespace ProteinFolding

open Computability

/-- Identity encoding of words over a finite alphabet. No padding or length prefix. -/
def wordEncoding (A : Type) [Fintype A] : FinEncoding (List A) where
  Γ := A
  ΓFin := inferInstance
  encode := id
  decode := some
  decode_encode _ := rfl

/-- Disjoint alphabets and one separator for a pair of encoded objects. -/
inductive PairSymbol (A B : Type) where
  | left : A → PairSymbol A B
  | sep : PairSymbol A B
  | right : B → PairSymbol A B
  deriving Fintype, DecidableEq

namespace PairSymbol

def readRight {A B : Type} : List (PairSymbol A B) → Option (List B)
  | [] => some []
  | right b :: w => (readRight w).map (b :: ·)
  | _ => none

def split {A B : Type} : List (PairSymbol A B) → Option (List A × List B)
  | sep :: w => (readRight w).map (fun bs => ([], bs))
  | left a :: w => (split w).map (fun ab => (a :: ab.1, ab.2))
  | _ => none

theorem readRight_map {A B : Type} (bs : List B) :
    readRight (bs.map (right (A := A))) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readRight, ih]

theorem split_join {A B : Type} (as : List A) (bs : List B) :
    split (as.map left ++ sep :: bs.map right) = some (as, bs) := by
  induction as with
  | nil => simp [split, readRight_map]
  | cons a as ih => simp [split, ih]

end PairSymbol

/-- Tagged concatenation with one separator. Its length is the sum of the two
component lengths plus one; tagging costs one symbol per original symbol.
Malformed tags/separators are rejected; component decoders handle their words. -/
def pairEncoding {A B : Type} (ea : FinEncoding A) (eb : FinEncoding B) :
    FinEncoding (A × B) where
  Γ := PairSymbol ea.Γ eb.Γ
  ΓFin := inferInstance
  encode ab := (ea.encode ab.1).map PairSymbol.left ++
    PairSymbol.sep :: (eb.encode ab.2).map PairSymbol.right
  decode w := do
    let (as, bs) ← PairSymbol.split w
    let a ← ea.decode as
    let b ← eb.decode bs
    pure (a, b)
  decode_encode ab := by
    simp [PairSymbol.split_join, ea.decode_encode, eb.decode_encode]

deriving instance Fintype for Residue

/-- Exactly one H/P alphabet symbol per residue, in the original order. -/
def sequenceEncoding : FinEncoding Sequence := wordEncoding Residue

/-- A sign bit followed by mathlib's little-endian binary magnitude.
False means nonnegative; true means negative. Zero has empty magnitude.
For a negative constructor `negSucc n`, the magnitude is n+1, not n. -/
def encodeSigned : ℤ → List Bool
  | .ofNat n => false :: encodeNat n
  | .negSucc n => true :: encodeNat (n + 1)

def decodeSigned : List Bool → Option ℤ
  | false :: bs => some (Int.ofNat (decodeNat bs))
  | true :: bs => some (-(Int.ofNat (decodeNat bs)))
  | [] => none

/-- Sign plus binary magnitude: length 1 + bitlength(|m|), with bitlength(0)=0.
This uses mathlib's binary natural encoding, never a unary magnitude.
The decoder may accept noncanonical words, but the encoder emits canonical ones. -/
def signedEncoding : FinEncoding ℤ where
  Γ := Bool
  ΓFin := inferInstance
  encode := encodeSigned
  decode := decodeSigned
  decode_encode z := by
    cases z <;> simp only [encodeSigned, decodeSigned, decode_encodeNat]
    rfl

end ProteinFolding
