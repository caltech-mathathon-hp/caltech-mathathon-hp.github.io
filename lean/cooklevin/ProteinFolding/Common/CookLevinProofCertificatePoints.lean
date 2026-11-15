import ProteinFolding.Common.CookLevinProofCertificateBoundary

/-! The certificate boundary as individual finite cell conditions. This
presentation has constant-arity alphabet and no-hole checks, plus fixed pins.
-/

namespace ProteinFolding.SAT.CookLevinCertificatePoints

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinLinks
open CookLevinCertificateCells CookLevinCertificateBoundary

theorem array_slice {D : Type*} {M : ℕ} (f : Fin M → D) (H B : ℕ) (h : H + B ≤ M) :
    ((List.ofFn f).drop H).take B =
      List.ofFn (fun i : Fin B => f ⟨H + i.val, by have hi := i.isLt; omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem array_prefix_iff {D : Type*} {M : ℕ} (f : Fin M → Option D) (header : List D)
    (h : header.length ≤ M) :
    (List.ofFn f).take header.length = header.map some ↔
      ∀ i : Fin header.length, f ⟨i.val, i.isLt.trans_le h⟩ = some header[i.val] := by
  have hs := array_slice f 0 header.length (by simpa using h)
  simp only [List.drop_zero, Nat.zero_add] at hs
  rw [hs, ← List.ofFn_getElem_eq_map header some, List.ofFn_inj, funext_iff]

theorem array_suffix_iff {D : Type*} {M : ℕ} (f : Fin M → Option D) (N : ℕ) (h : N ≤ M) :
    (List.ofFn f).drop N = List.replicate (M - N) none ↔
      ∀ i : Fin M, N ≤ i.val → f i = none := by
  constructor
  · intro he i hi
    have hj : i.val - N < M - N := by have hlt := i.isLt; omega
    have hget := congrArg (fun xs : List (Option D) => xs[i.val - N]?) he
    dsimp only at hget
    rw [List.getElem?_drop, List.getElem?_ofFn, List.getElem?_replicate] at hget
    have hsum : N + (i.val - N) = i.val := by omega
    simp only [hsum, dif_pos i.isLt, if_pos hj] at hget
    exact Option.some.inj hget
  · intro hall
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hni : N + i < M := by
      simp only [List.length_drop, List.length_ofFn] at hi
      omega
    have hf := hall ⟨N + i, hni⟩ (Nat.le_add_right N i)
    have he : f ⟨N + i, hni⟩ = x := by
      simpa only [List.getElem_drop, List.getElem_ofFn] using hix
    exact he.symm.trans hf

def headerIndex {M B : ℕ} (headerLength : ℕ) (h : headerLength + B ≤ M) (i : Fin headerLength) : Fin M :=
  ⟨i.val, by have hi := i.isLt; omega⟩

def certificateIndex {M B : ℕ} (headerLength : ℕ) (h : headerLength + B ≤ M) (i : Fin B) : Fin M :=
  ⟨headerLength + i.val, by have hi := i.isLt; omega⟩

def PointBoundary {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) (r : Row tm M) : Prop :=
  r.control = (some tm.main, tm.initialState) ∧
  (∀ i : Fin header.length, r.cells tm.k₀ (headerIndex header.length hM i) = some header[i.val]) ∧
  (∀ i : Fin B, r.cells tm.k₀ (certificateIndex header.length hM i) = none ∨
    ∃ c, r.cells tm.k₀ (certificateIndex header.length hM i) = some (e c)) ∧
  (∀ i j : Fin B, i < j → r.cells tm.k₀ (certificateIndex header.length hM i) = none →
    r.cells tm.k₀ (certificateIndex header.length hM j) = none) ∧
  (∀ i : Fin M, header.length + B ≤ i.val → r.cells tm.k₀ i = none) ∧
  ∀ k, k ≠ tm.k₀ → ∀ n, r.cells k n = none

theorem pointBoundary_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) (r : Row tm M) :
    PointBoundary tm M e header B hM r ↔ CertificateBoundary tm M e header B r := by
  have hp := array_prefix_iff (r.cells tm.k₀) header (by omega)
  have hs := array_suffix_iff (r.cells tm.k₀) (header.length + B) hM
  have ha := array_slice (r.cells tm.k₀) header.length B hM
  unfold PointBoundary CertificateBoundary HasCertificate inputCells
  rw [show M - header.length - B = M - (header.length + B) by omega]
  rw [hp, hs, ha]
  simp only [NoHoles, List.forall_mem_ofFn_iff, List.pairwise_ofFn, headerIndex,
    certificateIndex, and_assoc]

theorem pointBoundary_words_iff {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (hM : header.length + B ≤ M) (r : Row tm M) :
    PointBoundary tm M e header B hM r ↔ ∃ cs : List C, cs.length ≤ B ∧
      Represents r (initList tm ((header ++ cs.map e).map Subtype.val)) (initList_stacksIn tm _) := by
  rw [pointBoundary_iff, certificateBoundary_iff tm M e header B hM r]

end ProteinFolding.SAT.CookLevinCertificatePoints
