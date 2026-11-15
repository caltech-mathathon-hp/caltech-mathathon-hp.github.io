import ProteinFolding.Common.Complexity

/-!
# The Cook–Levin hypothesis (CNF-SAT is NP-hard)

CNF-SAT with variable indices in binary, and the statement that it is NP-hard
in the project's own sense (`ProteinFolding.NPHard`). This is intended to be
used ONLY as an explicit hypothesis `(hCL : CookLevin)`, never as an `axiom`.
-/

namespace ProteinFolding.SAT

open Computability

/-- A literal: a variable index and a polarity (`true` = positive). -/
structure Literal where
  var : ℕ
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Literal
abbrev CNF := List Clause

def Literal.eval (a : ℕ → Bool) (l : Literal) : Bool :=
  if l.pos then a l.var else !(a l.var)

/-- Standard CNF satisfiability; the empty clause is unsatisfiable and the
empty formula is satisfiable. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, l.eval a = true

/-- Five-symbol alphabet: binary digits, negation mark, two terminators. -/
inductive Sym where
  | bit : Bool → Sym
  | neg : Sym
  | endLit : Sym
  | endClause : Sym
  deriving DecidableEq, Fintype

/-! ### Generic terminator-delimited lists -/

section Terminated

variable {S α : Type} [DecidableEq S]

/-- Take the segment before the first `t`. -/
def takeSeg (t : S) : List S → Option (List S × List S)
  | [] => none
  | s :: w => if s = t then some ([], w) else (takeSeg t w).map (fun p => (s :: p.1, p.2))

theorem takeSeg_append (t : S) (u r : List S) (hu : t ∉ u) :
    takeSeg t (u ++ t :: r) = some (u, r) := by
  induction u with
  | nil => simp [takeSeg]
  | cons s u ih =>
    have hs : s ≠ t := fun h => hu (h ▸ List.mem_cons_self ..)
    have hu' : t ∉ u := fun h => hu (List.mem_cons_of_mem _ h)
    simp [takeSeg, hs, ih hu']

/-- Split a word into `t`-terminated segments (fuel = word length). -/
def segmentsF (t : S) : ℕ → List S → Option (List (List S))
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, s :: w =>
    match takeSeg t (s :: w) with
    | some (u, r) => (segmentsF t n r).map (u :: ·)
    | none => none

def allSome (dec : List S → Option α) : List (List S) → Option (List α)
  | [] => some []
  | w :: ws => do
    let a ← dec w
    let as ← allSome dec ws
    pure (a :: as)

/-- Each item's code followed by the terminator. -/
def encTerminated (t : S) (enc : α → List S) (xs : List α) : List S :=
  xs.flatMap (fun x => enc x ++ [t])

def decTerminated (t : S) (dec : List S → Option α) (w : List S) : Option (List α) :=
  (segmentsF t w.length w).bind (allSome dec)

theorem segmentsF_step (t : S) (u r : List S) (hu : t ∉ u) (m : ℕ) :
    segmentsF t (m + 1) (u ++ t :: r) = (segmentsF t m r).map (u :: ·) := by
  have h := takeSeg_append t u r hu
  cases hw : u ++ t :: r with
  | nil => simp at hw
  | cons s w =>
    rw [hw] at h
    simp only [segmentsF, h]

theorem segmentsF_enc (t : S) (us : List (List S)) (hus : ∀ u ∈ us, t ∉ u) :
    ∀ n, (us.flatMap (fun u => u ++ [t])).length ≤ n →
      segmentsF t n (us.flatMap (fun u => u ++ [t])) = some us := by
  induction us with
  | nil => intro n _; cases n <;> simp [segmentsF]
  | cons u us ih =>
    intro n hn
    have hu : t ∉ u := hus u (List.mem_cons_self ..)
    have hus' : ∀ v ∈ us, t ∉ v := fun v hv => hus v (List.mem_cons_of_mem _ hv)
    simp only [List.flatMap_cons, List.length_append, List.length_singleton] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hw : (u ++ [t]) ++ us.flatMap (fun u => u ++ [t]) =
        u ++ t :: us.flatMap (fun u => u ++ [t]) := by simp
    rw [List.flatMap_cons, hw, segmentsF_step t _ _ hu, ih hus' m (by omega)]
    rfl

omit [DecidableEq S] in
theorem allSome_map (enc : α → List S) (dec : List S → Option α)
    (h : ∀ x, dec (enc x) = some x) (xs : List α) :
    allSome dec (xs.map enc) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [allSome, h, ih]

theorem decTerminated_enc (t : S) (enc : α → List S) (dec : List S → Option α)
    (h : ∀ x, dec (enc x) = some x) (ht : ∀ x, t ∉ enc x) (xs : List α) :
    decTerminated t dec (encTerminated t enc xs) = some xs := by
  unfold decTerminated encTerminated
  have hflat : xs.flatMap (fun x => enc x ++ [t]) =
      (xs.map enc).flatMap (fun u => u ++ [t]) := by
    simp [List.flatMap_map]
  have hmem : ∀ u ∈ xs.map enc, t ∉ u := by
    intro u hu
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hu
    exact ht x
  rw [hflat, segmentsF_enc t (xs.map enc) hmem _ le_rfl]
  simpa using allSome_map enc dec h xs

end Terminated

/-! ### The SAT encoding -/

def bitsOf : List Sym → Option (List Bool)
  | [] => some []
  | .bit b :: w => (bitsOf w).map (b :: ·)
  | _ => none

theorem bitsOf_map (bs : List Bool) : bitsOf (bs.map Sym.bit) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bitsOf, ih]

/-- Optional negation mark, then the little-endian binary index (mathlib's
`encodeNat`, no unary field). -/
def encodeLit (l : Literal) : List Sym :=
  (if l.pos then [] else [Sym.neg]) ++ (encodeNat l.var).map Sym.bit

def decodeLit : List Sym → Option Literal
  | .neg :: w => (bitsOf w).map fun bs => ⟨decodeNat bs, false⟩
  | w => (bitsOf w).map fun bs => ⟨decodeNat bs, true⟩

theorem decodeLit_encodeLit (l : Literal) : decodeLit (encodeLit l) = some l := by
  obtain ⟨v, p⟩ := l
  cases p
  · simp [encodeLit, decodeLit, bitsOf_map]
  · cases h : encodeNat v with
    | nil =>
      simp [encodeLit, decodeLit, h, bitsOf]
      rw [← h, decode_encodeNat]
    | cons b bs =>
      simp only [encodeLit, if_true, List.nil_append, h, List.map_cons, decodeLit]
      rw [← List.map_cons, bitsOf_map]
      simp [← h]

def encodeClause (c : Clause) : List Sym := encTerminated Sym.endLit encodeLit c

def decodeClause (w : List Sym) : Option Clause := decTerminated Sym.endLit decodeLit w

theorem decodeClause_encodeClause (c : Clause) : decodeClause (encodeClause c) = some c :=
  decTerminated_enc _ _ _ decodeLit_encodeLit
    (fun l => by unfold encodeLit; split <;> simp) c

/-- A CNF is its clauses, each followed by `endClause`; each clause is its
literals, each followed by `endLit`. Length is linear in the formula's size with
binary indices. -/
def cnfEncoding : FinEncoding CNF where
  Γ := Sym
  ΓFin := inferInstance
  encode := encTerminated Sym.endClause encodeClause
  decode := decTerminated Sym.endClause decodeClause
  decode_encode :=
    decTerminated_enc _ _ _ decodeClause_encodeClause
      (fun c => by
        unfold encodeClause encTerminated encodeLit
        simp only [List.mem_flatMap, List.mem_append, not_exists, not_and]
        intro l _
        split <;> simp)

/-- **The Cook–Levin hypothesis**: CNF-SAT (binary indices) is NP-hard in the
project's sense. Use only as an explicit hypothesis. -/
def CookLevin : Prop := NPHard cnfEncoding Satisfiable

/-! ### Sanity checks on `Satisfiable` -/

example : Satisfiable [] := ⟨fun _ => true, by simp⟩
example : ¬ Satisfiable [[]] := by
  rintro ⟨a, h⟩
  simpa using h [] (by simp)
example : Satisfiable [[⟨0, true⟩]] := ⟨fun _ => true, by simp [Literal.eval]⟩
example : ¬ Satisfiable [[⟨0, true⟩], [⟨0, false⟩]] := by
  rintro ⟨a, h⟩
  have h1 := h _ (List.mem_cons_self ..)
  have h2 := h [⟨0, false⟩] (by simp)
  simp [Literal.eval] at h1 h2
  simp [h1] at h2

end ProteinFolding.SAT
