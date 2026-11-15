import ProteinFolding.Common.Encodings
import Mathlib.Computability.TMComputable

/-!
# Complexity predicates on finitely encoded types

These definitions supply the meaning of NP-completeness in both the square
and cubic developments. The computational model and time bounds come directly
from mathlib's `Turing.TM2ComputableInPolyTime`.
No completeness of SAT or of any packing problem is assumed.

All problem and certificate types are explicitly in `Type` (universe zero),
as required by this pinned mathlib machine API. Hardness quantifies over EVERY
such type and EVERY finite encoding, not just the project's instance types.
-/

namespace ProteinFolding

open Computability Turing

/-- A total Boolean decider on encoded inputs, with a polynomial TM2 time bound.
The machine structure is data, so `Nonempty` turns its existence into a Prop.
As in mathlib, behavior outside the image of the input encoding is unspecified. -/
def PolyTimeDecidable {A : Type} (ea : FinEncoding A) (L : A → Prop) : Prop :=
  ∃ f : A → Bool,
    Nonempty (TM2ComputableInPolyTime ea finEncodingBoolBool f) ∧
      ∀ x, f x = true ↔ L x

/-- The polynomially bounded verifier definition of NP.

The certificate encoder must cover all words over its alphabet. This prevents
an arbitrary encoding image from hiding an undecidable certificate-validity
condition. Ordinary finite-word certificates with `wordEncoding` satisfy this
condition directly. The verifier runs on `pairEncoding ea ec`, whose length is
the input length plus certificate length plus one. Both lengths in the bound
are actual encoding lengths; p has natural coefficients.

This is a predicate definition, not a proof of membership for any HP problem. -/
def InNP {A : Type} (ea : FinEncoding A) (L : A → Prop) : Prop :=
  ∃ (C : Type) (ec : FinEncoding C),
    Function.Surjective ec.encode ∧
    ∃ (p : Polynomial ℕ) (R : A × C → Prop),
      PolyTimeDecidable (pairEncoding ea ec) R ∧
        ∀ x, L x ↔ ∃ c, (ec.encode c).length ≤ p.eval (ea.encode x).length ∧ R (x, c)

/-- Karp (polynomial-time many-one) reducibility, for independently encoded types.
The reducing function is total and preserves both yes- and no-instances. -/
def KarpReduces {A B : Type} (ea : FinEncoding A) (eb : FinEncoding B)
    (L : A → Prop) (M : B → Prop) : Prop :=
  ∃ f : A → B,
    Nonempty (TM2ComputableInPolyTime ea eb f) ∧ ∀ x, L x ↔ M (f x)

/-- Universal NP-hardness, not hardness relative to an assumed complete problem.
The source type is in universe zero, just as in mathlib's TM2 computation API. -/
def NPHard {A : Type} (ea : FinEncoding A) (L : A → Prop) : Prop :=
  ∀ (B : Type) (eb : FinEncoding B) (M : B → Prop),
    InNP eb M → KarpReduces eb ea M L

/-- Membership in NP together with universal Karp NP-hardness. -/
def NPComplete {A : Type} (ea : FinEncoding A) (L : A → Prop) : Prop :=
  InNP ea L ∧ NPHard ea L

end ProteinFolding
