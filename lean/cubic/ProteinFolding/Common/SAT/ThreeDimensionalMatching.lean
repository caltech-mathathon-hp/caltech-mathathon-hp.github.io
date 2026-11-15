import ProteinFolding.Common.CookLevin
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Range

/-! Balanced three-dimensional matching on explicit finite vertex sets.
The three coordinate sets are separate copies of `{0,...,n-1}`. A matching
selects occurrences from the supplied triple list and covers every coordinate
exactly once. All raw numerical fields use unary encodings, so the entire
finite universe is explicitly represented, even for an empty triple list.
This presentation carries no hardness assumption. -/

namespace ProteinFolding.ThreeDimensionalMatching

open Computability

abbrev Triple := ℕ × ℕ × ℕ

structure Instance where
  size : ℕ
  triples : List Triple
  deriving DecidableEq, Repr

def WellFormed (I : Instance) : Prop :=
  ∀ t ∈ I.triples, t.1 < I.size ∧ t.2.1 < I.size ∧ t.2.2 < I.size

def Matches (I : Instance) (chosen : List Triple) : Prop :=
  chosen.Subperm I.triples ∧
    (chosen.map Prod.fst).Perm (List.range I.size) ∧
    (chosen.map (fun t => t.2.1)).Perm (List.range I.size) ∧
    (chosen.map (fun t => t.2.2)).Perm (List.range I.size)

def Accepts (I : Instance) : Prop := WellFormed I ∧ ∃ chosen, Matches I chosen

def tripleFieldsEncoding : FinEncoding Triple :=
  pairEncoding unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)

instance : DecidableEq tripleFieldsEncoding.Γ :=
  inferInstanceAs (DecidableEq (PairSymbol Bool (PairSymbol Bool Bool)))

def encodeTriple (t : Triple) : List (Option tripleFieldsEncoding.Γ) :=
  (tripleFieldsEncoding.encode t).map some

def decodeTriple (w : List (Option tripleFieldsEncoding.Γ)) : Option Triple :=
  tripleFieldsEncoding.decode (w.filterMap id)

theorem decodeTriple_encodeTriple (t : Triple) : decodeTriple (encodeTriple t) = some t := by
  simpa [decodeTriple, encodeTriple, List.filterMap_map, Function.comp_def] using
    tripleFieldsEncoding.decode_encode t

theorem encodeTriple_no_none (t : Triple) : none ∉ encodeTriple t := by simp [encodeTriple]

/-- One terminator per triple; pair tags separate its three unary coordinates.
No list length, vertex field, or coordinate is padded. -/
def triplesEncoding : FinEncoding (List Triple) where
  Γ := Option tripleFieldsEncoding.Γ
  ΓFin := inferInstance
  encode := SAT.encTerminated none encodeTriple
  decode := SAT.decTerminated none decodeTriple
  decode_encode ts := SAT.decTerminated_enc none encodeTriple decodeTriple
    decodeTriple_encodeTriple encodeTriple_no_none ts

def fieldsEncoding : FinEncoding (ℕ × List Triple) :=
  pairEncoding unaryFinEncodingNat triplesEncoding

/-- Explicit unary universe size plus a terminator-delimited list of triples.
This is polynomially equivalent to the usual explicit-universe presentation:
well-formed coordinate values are smaller than the explicitly encoded size. -/
def instanceEncoding : FinEncoding Instance where
  Γ := fieldsEncoding.Γ
  ΓFin := inferInstance
  encode I := fieldsEncoding.encode (I.size, I.triples)
  decode w := (fieldsEncoding.decode w).map (fun p => ⟨p.1, p.2⟩)
  decode_encode I := by
    rw [fieldsEncoding.decode_encode]
    cases I
    rfl

theorem matches_length {I : Instance} {chosen : List Triple} (h : Matches I chosen) :
    chosen.length = I.size := by
  simpa using h.2.1.length_eq

theorem matches_nodup {I : Instance} {chosen : List Triple} (h : Matches I chosen) :
    chosen.Nodup := by
  have hm : (chosen.map Prod.fst).Nodup := h.2.1.nodup_iff.mpr List.nodup_range
  exact List.Nodup.of_map Prod.fst hm

theorem matches_coordinates {I : Instance} {chosen : List Triple} (h : Matches I chosen)
    (t : Triple) (ht : t ∈ chosen) : t.1 < I.size ∧ t.2.1 < I.size ∧ t.2.2 < I.size := by
  constructor
  · have hm := h.2.1.mem_iff.mp (List.mem_map.mpr ⟨t, ht, rfl⟩)
    exact List.mem_range.mp hm
  · constructor
    · have hm := h.2.2.1.mem_iff.mp (List.mem_map.mpr ⟨t, ht, rfl⟩)
      exact List.mem_range.mp hm
    · have hm := h.2.2.2.mem_iff.mp (List.mem_map.mpr ⟨t, ht, rfl⟩)
      exact List.mem_range.mp hm

def UnaryThreeDimensionalMatchingNPHard : Prop := NPHard instanceEncoding Accepts

example : Accepts ⟨0, []⟩ := by
  refine ⟨by simp [WellFormed], [], ?_⟩
  simp [Matches]

example : ¬ Accepts ⟨1, []⟩ := by
  rintro ⟨_, chosen, hc⟩
  have hl := matches_length hc
  have hs : chosen.length ≤ 0 := hc.1.length_le
  change chosen.length = 1 at hl
  omega

end ProteinFolding.ThreeDimensionalMatching
