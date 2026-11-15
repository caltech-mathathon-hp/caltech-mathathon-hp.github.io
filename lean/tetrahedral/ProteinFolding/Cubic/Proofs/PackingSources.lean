import ProteinFolding.Common.CookLevin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Linarith

/-! Unary packing source problems from Berger--Leighton, Section 2 (p. 31).
Items are list occurrences, so repeated sizes remain distinct items. A packing
lists its bins and requires their flattened sizes to be a permutation of the
input. Thus every occurrence is assigned exactly once; empty bins are allowed.

All numerical fields have unary encodings. This is the strongly NP-hard source
presentation needed by a reduction whose output grows with the item sizes.
No source hardness or polynomial-time reduction is assumed in this file. -/

namespace ProteinFolding.Packing

open Computability

structure Instance where
  sizes : List ℕ
  capacity : ℕ
  bins : ℕ
  deriving DecidableEq, Repr

def WellFormed (I : Instance) : Prop :=
  0 < I.capacity ∧ 0 < I.bins ∧ ∀ s ∈ I.sizes, 0 < s

def Fits (I : Instance) (parts : List (List ℕ)) : Prop :=
  parts.length = I.bins ∧ I.sizes.Perm parts.flatten ∧
    ∀ p ∈ parts, p.sum ≤ I.capacity

def Exact (I : Instance) (parts : List (List ℕ)) : Prop :=
  parts.length = I.bins ∧ I.sizes.Perm parts.flatten ∧
    ∀ p ∈ parts, p.sum = I.capacity

/-- Garey--Johnson BIN PACKING: positive sizes, capacity, and number of bins;
every bin has load at most the capacity (Section 2, p. 31). -/
def BinAccepts (I : Instance) : Prop := WellFormed I ∧ ∃ parts, Fits I parts

/-- The saturated restriction of BIN PACKING, useful before doubling sizes. -/
def SaturatedBinAccepts (I : Instance) : Prop :=
  BinAccepts I ∧ I.sizes.sum = I.capacity * I.bins

/-- MODIFIED BIN PACKING (Section 2, p. 31): positive even sizes, positive B,K,
total size B*K, and a partition with every bin load exactly B. Ill-formed raw
inputs are no-instances. -/
def ModifiedAccepts (I : Instance) : Prop :=
  WellFormed I ∧ (∀ s ∈ I.sizes, Even s) ∧
    I.sizes.sum = I.capacity * I.bins ∧ ∃ parts, Exact I parts

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryEncodeNat] using congrArg Nat.succ ih

theorem unary_no_false (n : ℕ) : false ∉ unaryEncodeNat n := by
  induction n with
  | zero => simp [unaryEncodeNat]
  | succ n ih => simp [unaryEncodeNat, ih]

/-- Each unary item is terminated by false. Empty lists and zero-sized items
have distinct encodings; zero-sized items are rejected by the problem predicate. -/
def itemEncoding : FinEncoding (List ℕ) where
  Γ := Bool
  ΓFin := inferInstance
  encode := SAT.encTerminated false unaryEncodeNat
  decode := SAT.decTerminated false (fun w => some w.length)
  decode_encode xs := SAT.decTerminated_enc false unaryEncodeNat (fun w : List Bool => some w.length)
    (fun n => congrArg some (unary_length n)) unary_no_false xs

theorem itemEncoding_length (xs : List ℕ) :
    (itemEncoding.encode xs).length = xs.sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [itemEncoding, SAT.encTerminated, List.flatMap_cons, List.length_append,
      unary_length, List.sum_cons, List.length_cons, List.length_nil] at *
    omega

def fieldsEncoding : FinEncoding (List ℕ × (ℕ × ℕ)) :=
  pairEncoding itemEncoding (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)

/-- Unary item sizes, capacity and bin count with tagged field separators.
Length is sum(sizes)+number_of_items+B+K+2. No padding or inflated field is used;
on strongly bounded source families this is polynomial in the original input. -/
def instanceEncoding : FinEncoding Instance where
  Γ := fieldsEncoding.Γ
  ΓFin := inferInstance
  encode I := fieldsEncoding.encode (I.sizes, (I.capacity, I.bins))
  decode w := (fieldsEncoding.decode w).map fun p => ⟨p.1, p.2.1, p.2.2⟩
  decode_encode I := by
    rw [fieldsEncoding.decode_encode]
    cases I
    rfl

theorem instanceEncoding_length (I : Instance) :
    (instanceEncoding.encode I).length =
      I.sizes.sum + I.sizes.length + I.capacity + I.bins + 2 := by
  simp [instanceEncoding, fieldsEncoding, pairEncoding, unaryFinEncodingNat,
    itemEncoding_length, unary_length]
  omega

def BinPackingUnaryNPHard : Prop := NPHard instanceEncoding BinAccepts

def ModifiedBinPackingUnaryNPHard : Prop := NPHard instanceEncoding ModifiedAccepts

theorem exact_fits {I : Instance} {parts : List (List ℕ)} (h : Exact I parts) : Fits I parts :=
  ⟨h.1, h.2.1, fun p hp => (h.2.2 p hp).le⟩

theorem bin_load_bound (B : ℕ) (parts : List (List ℕ))
    (h : ∀ p ∈ parts, p.sum ≤ B) : parts.flatten.sum ≤ B * parts.length := by
  induction parts with
  | nil => simp
  | cons p parts ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [List.flatten_cons, List.sum_append, List.length_cons]
    nlinarith

/-- Saturation removes the distinction between capacity inequalities and exact
loads. This uses every item occurrence and permits empty bins only when B=0. -/
theorem exact_of_fits_of_total {I : Instance} {parts : List (List ℕ)}
    (h : Fits I parts) (ht : I.sizes.sum = I.capacity * I.bins) : Exact I parts := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hs : parts.flatten.sum = I.capacity * parts.length := by
    rw [← h.2.1.sum_eq, h.1, ht]
  have hb := h.2.2
  clear ht h
  induction parts with
  | nil => simp
  | cons p parts ih =>
    have hp := hb p (by simp)
    have ht := bin_load_bound I.capacity parts (fun q hq => hb q (by simp [hq]))
    simp only [List.flatten_cons, List.sum_append, List.length_cons] at hs
    have he : p.sum = I.capacity := by nlinarith
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact he
    · exact ih (by nlinarith) (fun r hr => hb r (by simp [hr])) q hq

theorem saturated_iff_exact (I : Instance) :
    SaturatedBinAccepts I ↔
      WellFormed I ∧ I.sizes.sum = I.capacity * I.bins ∧ ∃ parts, Exact I parts := by
  constructor
  · rintro ⟨⟨hw, parts, hp⟩, ht⟩
    exact ⟨hw, ht, parts, exact_of_fits_of_total hp ht⟩
  · rintro ⟨hw, ht, parts, hp⟩
    exact ⟨⟨hw, parts, exact_fits hp⟩, ht⟩

end ProteinFolding.Packing
