import ProteinFolding.Common.TM2WalkCopy
import ProteinFolding.Common.TM2Renaming
import ProteinFolding.Common.TM2CompositionPoly

/-! A reusable finite-stack program for mapping a polynomial-time word-valued
function over encoded records while preserving a shared parameter. The run and
polynomial-time proofs are separate modules. This file defines the actual
program and its unambiguous record-list encoding. -/

namespace ProteinFolding.TM2ListMap

open Computability Turing TM2

def splitFields {A : Type} : List (Option A) → Option (List (List A))
  | [] => some []
  | none :: w => (splitFields w).map ([] :: ·)
  | some a :: w => do
    let fields ← splitFields w
    match fields with
    | [] => none
    | f :: fs => some ((a :: f) :: fs)

def encodeFields {A : Type} (e : FinEncoding A) : List A → List (Option e.Γ)
  | [] => []
  | a :: as => (e.encode a).map some ++ none :: encodeFields e as

theorem splitFields_prefix {A : Type} (a : List A) (w : List (Option A)) :
    splitFields (a.map some ++ none :: w) = (splitFields w).map (a :: ·) := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, splitFields, ih]
    cases splitFields w <;> rfl

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

/-- Every field has one terminator; its letters have `some` tags. The length
is the sum of the component encoding lengths plus the number of records. -/
def listEncoding {A : Type} (e : FinEncoding A) : FinEncoding (List A) where
  Γ := Option e.Γ
  ΓFin := inferInstance
  encode := encodeFields e
  decode w := do
    let fields ← splitFields w
    fields.mapM e.decode
  decode_encode as := by rw [splitFields_encode]; exact decodeFields_encode e as

section Machine

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

abbrev InLetter := h.tm.Γ h.tm.k₀
abbrev OutLetter := h.tm.Γ h.tm.k₁
abbrev RawSymbol := PairSymbol ep.Γ (Option ea.Γ)

inductive Extra where
  | input | parameter | parameterBuffer | record | accumulator | output
  deriving DecidableEq, Fintype

inductive Label (Λ : Type) where
  | parameter | record | restoreRecord | separator | copyParameter | restoreParameter
  | child : Λ → Label Λ
  | drainChild | clearParameter | output | finish
  deriving DecidableEq, Fintype

abbrev Stack := h.tm.K ⊕ Extra
abbrev Caches := Option (InLetter h) × Option (OutLetter h)
abbrev State := h.tm.σ × Caches h
abbrev Phase := Label h.tm.Λ

def ExtraAlphabet : Extra → Type
  | .input => RawSymbol (ep := ep) (ea := ea)
  | .parameter | .parameterBuffer | .record => InLetter h
  | .accumulator => OutLetter h
  | .output => B

abbrev Alphabet : Stack h → Type := Sum.elim h.tm.Γ (ExtraAlphabet h)

def separator : InLetter h := h.inputAlphabet.symm .sep

def outputSymbol (a : OutLetter h) : B := h.outputAlphabet a

def inputEquiv : ((h.tm.σ × Option (OutLetter h)) × Option (InLetter h)) ≃ State h where
  toFun st := (st.1.1, (st.2, st.1.2))
  invFun st := ((st.1, st.2.2), st.2.1)
  left_inv st := by obtain ⟨⟨s, o⟩, i⟩ := st; rfl
  right_inv st := by obtain ⟨s, i, o⟩ := st; rfl

def outputEquiv : ((h.tm.σ × Option (InLetter h)) × Option (OutLetter h)) ≃ State h where
  toFun st := (st.1.1, (st.1.2, st.2))
  invFun st := ((st.1, st.2.1), st.2.2)
  left_inv st := by obtain ⟨⟨s, i⟩, o⟩ := st; rfl
  right_inv st := by obtain ⟨s, i, o⟩ := st; rfl

def rawToInput : RawSymbol (ep := ep) (ea := ea) → InLetter h
  | .left p => h.inputAlphabet.symm (.left p)
  | .right (some a) => h.inputAlphabet.symm (.right a)
  | _ => separator h

def isSeparator (a : InLetter h) : Bool :=
  match h.inputAlphabet a with | .sep => true | _ => false

def initial : State h := (h.tm.initialState, (none, none))

def inputTransfer (src dst : Stack h)
    (hs : Alphabet h src = InLetter h) (hd : Alphabet h dst = InLetter h)
    (loop finalLabel : Phase h) : Stmt (Alphabet h) (Phase h) (State h) := by
  letI : Inhabited (Alphabet h src) := ⟨cast hs.symm (separator h)⟩
  let e := (Equiv.prodCongr (Equiv.refl (h.tm.σ × Option (OutLetter h)))
    (Equiv.optionCongr (Equiv.cast hs))).trans (inputEquiv h)
  exact TM2Renaming.relabelStmt e
    (TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
      (σ := h.tm.σ × Option (OutLetter h)) src dst
      (fun a : Alphabet h src => cast hd.symm (cast hs a)) loop finalLabel)

def outputTransfer [Inhabited B] (src dst : Stack h)
    (hs : Alphabet h src = OutLetter h) (convert : OutLetter h → Alphabet h dst)
    (loop finalLabel : Phase h) : Stmt (Alphabet h) (Phase h) (State h) := by
  letI : Inhabited (Alphabet h src) := ⟨cast hs.symm (h.outputAlphabet.symm (default : B))⟩
  let e := (Equiv.prodCongr (Equiv.refl (h.tm.σ × Option (InLetter h)))
    (Equiv.optionCongr (Equiv.cast hs))).trans (outputEquiv h)
  exact TM2Renaming.relabelStmt e
    (TM2Transfer.transferStmt (Γ := Alphabet h) (Λ := Phase h)
      (σ := h.tm.σ × Option (InLetter h)) src dst
      (fun a : Alphabet h src => convert (cast hs a)) loop finalLabel)

def copyParameter : Stmt (Alphabet h) (Phase h) (State h) := by
  letI : Inhabited (Alphabet h (.inr .parameter)) := ⟨separator h⟩
  exact TM2Renaming.relabelStmt (inputEquiv h)
    (TM2WalkCopy.duplicateStmt (Γ := Alphabet h) (L := Phase h)
      (σ := h.tm.σ × Option (OutLetter h)) (.inr .parameter) (.inr .parameterBuffer) (.inl h.tm.k₀)
      id id .copyParameter .restoreParameter)

def program [Inhabited B] : Phase h → Stmt (Alphabet h) (Phase h) (State h)
  | .parameter => .pop (.inr .input) (fun st head => (st.1, (head.map (rawToInput h), st.2.2)))
      (.branch (fun st => st.2.1.isSome)
        (.branch (fun st => (st.2.1.map (isSeparator h)).getD false)
          (.load (fun st => (st.1, (none, st.2.2))) (.goto (fun _ => .record)))
          (.push (.inr .parameter) (fun st => st.2.1.getD (separator h))
            (.goto (fun _ => .parameter))))
        (.load (fun st => (st.1, (none, st.2.2))) (.goto (fun _ => .clearParameter))))
  | .record => .pop (.inr .input) (fun st head => (st.1, (head.map (rawToInput h), st.2.2)))
      (.branch (fun st => st.2.1.isSome)
        (.branch (fun st => (st.2.1.map (isSeparator h)).getD false)
          (.load (fun st => (st.1, (none, st.2.2))) (.goto (fun _ => .restoreRecord)))
          (.push (.inr .record) (fun st => st.2.1.getD (separator h)) (.goto (fun _ => .record))))
        (.load (fun st => (st.1, (none, st.2.2))) (.goto (fun _ => .clearParameter))))
  | .restoreRecord => inputTransfer h (.inr .record) (.inl h.tm.k₀) rfl rfl .restoreRecord .separator
  | .separator => .push (.inl h.tm.k₀) (fun _ => separator h) (.goto (fun _ => .copyParameter))
  | .copyParameter => copyParameter h
  | .restoreParameter => inputTransfer h (.inr .parameterBuffer) (.inr .parameter) rfl rfl
      .restoreParameter (.child h.tm.main)
  | .child l => TM2Embedding.liftStmt Label.child (some .drainChild) (h.tm.m l)
  | .drainChild => outputTransfer h (.inl h.tm.k₁) (.inr .accumulator) rfl id .drainChild .record
  | .clearParameter => .pop (.inr .parameter) (fun st head => (st.1, (head, st.2.2)))
      (.branch (fun st => st.2.1.isSome) (.goto (fun _ => .clearParameter))
        (.load (fun st => (st.1, (none, st.2.2))) (.goto (fun _ => .output))))
  | .output => outputTransfer h (.inr .accumulator) (.inr .output) rfl
      h.outputAlphabet .output .finish
  | .finish => .load (fun _ => initial h) .halt

def extraContents (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (parameter record buffer : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    ∀ k, List (ExtraAlphabet h k)
  | .input => raw
  | .parameter => parameter
  | .parameterBuffer => buffer
  | .record => record
  | .accumulator => acc
  | .output => out

def contents (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (parameter record buffer : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    ∀ k, List (Alphabet h k) := TM2Embedding.joinStacks S (extraContents h raw parameter record buffer acc out)

def cfg (p : Phase h) (st : State h) (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (parameter record buffer : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    Cfg (Alphabet h) (Phase h) (State h) := ⟨some p, st, contents h S raw parameter record buffer acc out⟩

def run [Inhabited B] (n : ℕ) (q : Cfg (Alphabet h) (Phase h) (State h)) :
    Option (Cfg (Alphabet h) (Phase h) (State h)) :=
  (fun x : Option (Cfg (Alphabet h) (Phase h) (State h)) => x.bind (step (program h)))^[n] (some q)

theorem run_step [Inhabited B] {q q' : Cfg (Alphabet h) (Phase h) (State h)}
    (hst : step (program h) q = some q') (n : ℕ) : run h (n + 1) q = run h n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, hst]

theorem run_add [Inhabited B] {q q' : Cfg (Alphabet h) (Phase h) (State h)} {n : ℕ}
    (hr : run h n q = some q') (m : ℕ) : run h (n + m) q = run h m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet h) (Phase h) (State h)) => x.bind (step (program h)))^[n]
      (some q) = some q' from hr]

end Machine

end ProteinFolding.TM2ListMap
