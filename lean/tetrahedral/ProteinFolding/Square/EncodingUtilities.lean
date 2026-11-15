import ProteinFolding.Common.Encodings

namespace ProteinFolding.Square

open Computability

/-- A separator terminates each field, so empty fields and an empty list differ. -/
def splitFields {A : Type} : List (Option A) → Option (List (List A))
  | [] => some []
  | none :: w => (splitFields w).map ([] :: ·)
  | some a :: w => do
    let fields ← splitFields w
    match fields with
    | [] => none
    | f :: fs => some ((a :: f) :: fs)

theorem splitFields_prefix {A : Type} (a : List A) (w : List (Option A)) :
    splitFields (a.map some ++ none :: w) = (splitFields w).map (a :: ·) := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, splitFields, ih]
    cases splitFields w <;> rfl

def encodeFields {A : Type} (e : FinEncoding A) : List A → List (Option e.Γ)
  | [] => []
  | a :: as => (e.encode a).map some ++ none :: encodeFields e as

theorem splitFields_encode {A : Type} (e : FinEncoding A) (as : List A) :
    splitFields (encodeFields e as) = some (as.map e.encode) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [encodeFields, splitFields_prefix, ih]; rfl

theorem decodeFields_encode {A : Type} (e : FinEncoding A) (as : List A) :
    (as.map e.encode).mapM e.decode = some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [e.decode_encode, ih]

/-- Explicit finite-word encoding of a list of independently encoded objects. -/
def listEncoding {A : Type} (e : FinEncoding A) : FinEncoding (List A) where
  Γ := Option e.Γ
  ΓFin := inferInstance
  encode := encodeFields e
  decode w := do
    let fields ← splitFields w
    fields.mapM e.decode
  decode_encode as := by rw [splitFields_encode]; exact decodeFields_encode e as

end ProteinFolding.Square
