import ProteinFolding.Common.CookLevinProofGlobalCNF
import Mathlib.Data.List.OfFn

/-! Bounded certificate words in a concrete initial TM2 row. The header is
fixed, each remaining occupied cell carries a certificate-alphabet symbol,
and empty cells cannot be followed by occupied cells. This describes arbitrary
words of length at most B without enumerating exponentially many words.
-/

namespace ProteinFolding.SAT.CookLevinCertificateCells

open Turing TM2 CookLevinAlphabet CookLevinRows CookLevinLinks

def padded {D : Type*} (xs : List D) (M : ℕ) : List (Option D) :=
  xs.map some ++ List.replicate (M - xs.length) none

theorem padded_length {D : Type*} (xs : List D) (M : ℕ) (h : xs.length ≤ M) :
    (padded xs M).length = M := by simp only [padded, List.length_append, List.length_map, List.length_replicate]; omega

theorem padded_ofFn {D : Type*} (xs : List D) (M : ℕ) (h : xs.length ≤ M) :
    List.ofFn (fun i : Fin M => xs[i.val]?) = padded xs M := by
  induction xs generalizing M with
  | nil => simp [padded]
  | cons x xs ih =>
    cases M with
    | zero => simp at h
    | succ M =>
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, List.getElem?_cons_zero, Fin.val_succ, List.getElem?_cons_succ]
      rw [ih M (by simpa using h)]
      simp [padded]

def NoHoles {D : Type*} (ys : List (Option D)) : Prop :=
  ys.Pairwise (fun x y => x = none → y = none)

theorem padded_noHoles {D : Type*} (xs : List D) (M : ℕ) : NoHoles (padded xs M) := by
  unfold NoHoles padded
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_of_forall (by intro x y h; cases h)
  · intro x hx y _ hn
    obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
    contradiction

theorem noHoles_image_word {C D : Type*} (e : C → D) (ys : List (Option D))
    (ha : ∀ y ∈ ys, y = none ∨ ∃ c, y = some (e c)) (hn : NoHoles ys) :
    ∃ cs : List C, cs.length ≤ ys.length ∧ ys = padded (cs.map e) ys.length := by
  induction ys with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons y ys ih =>
    have hp := List.pairwise_cons.mp hn
    cases y with
    | none =>
      refine ⟨[], by simp, ?_⟩
      have he : ys = List.replicate ys.length none := List.eq_replicate_iff.mpr
        ⟨rfl, fun z hz => hp.1 z hz rfl⟩
      simp only [padded, List.map_nil, List.length_nil, Nat.sub_zero, List.nil_append, List.length_cons]
      rw [he, List.replicate_succ]
      simp
    | some d =>
      have hc := ha (some d) (List.mem_cons_self ..)
      rcases hc with hc | ⟨c, hc⟩
      · contradiction
      · have hd : d = e c := Option.some.inj hc
        subst d
        obtain ⟨cs, hcs, he⟩ := ih (fun z hz => ha z (List.mem_cons_of_mem _ hz)) hp.2
        refine ⟨c :: cs, by simpa using hcs, ?_⟩
        simpa [padded] using congrArg (some (e c) :: ·) he

theorem padded_split {D : Type*} (header cert : List D) (B M : ℕ)
    (hc : cert.length ≤ B) (hM : header.length + B ≤ M) :
    padded (header ++ cert) M =
      header.map some ++ padded cert B ++ List.replicate (M - header.length - B) none := by
  have hp : M - (header.length + cert.length) = (B - cert.length) + (M - header.length - B) := by omega
  simp only [padded, List.map_append, List.length_append, hp, List.replicate_add, List.append_assoc]

theorem list_segments {D : Type*} (xs ys zs : List D) :
    (xs ++ ys ++ zs).take xs.length = xs ∧
    ((xs ++ ys ++ zs).drop xs.length).take ys.length = ys ∧
    (xs ++ ys ++ zs).drop (xs.length + ys.length) = zs := by
  simp [List.append_assoc, List.drop_append]

def HasCertificate {C D : Type*} (e : C → D) (header : List D) (B M : ℕ) (cells : List (Option D)) : Prop :=
  cells.take header.length = header.map some ∧
  (∀ y ∈ (cells.drop header.length).take B, y = none ∨ ∃ c, y = some (e c)) ∧
  NoHoles ((cells.drop header.length).take B) ∧
  cells.drop (header.length + B) = List.replicate (M - header.length - B) none

theorem hasCertificate_iff {C D : Type*} (e : C → D) (header : List D) (B M : ℕ)
    (cells : List (Option D)) (hlen : cells.length = M) (hM : header.length + B ≤ M) :
    HasCertificate e header B M cells ↔
      ∃ cs : List C, cs.length ≤ B ∧ cells = padded (header ++ cs.map e) M := by
  constructor
  · rintro ⟨hh, ha, hn, hs⟩
    have hl : ((cells.drop header.length).take B).length = B := by
      simp only [List.length_take, List.length_drop, hlen]
      omega
    obtain ⟨cs, hcs, hc⟩ := noHoles_image_word e _ ha hn
    rw [hl] at hcs hc
    refine ⟨cs, hcs, ?_⟩
    have hd : cells = cells.take header.length ++ (cells.drop header.length).take B ++
        cells.drop (header.length + B) := by
      rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]
    rw [hd, hh, hc, hs]
    exact (padded_split header (cs.map e) B M (by simpa using hcs) hM).symm
  · rintro ⟨cs, hcs, rfl⟩
    rw [padded_split header (cs.map e) B M (by simpa using hcs) hM]
    have hseg := list_segments (header.map some) (padded (cs.map e) B)
      (List.replicate (M - header.length - B) (none : Option D))
    simp only [List.length_map, padded_length (cs.map e) B (by simpa using hcs)] at hseg
    refine ⟨hseg.1, ?_, ?_, hseg.2.2⟩
    · rw [hseg.2.1]
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hd
        exact Or.inr ⟨c, rfl⟩
      · exact Or.inl (List.eq_of_mem_replicate hy)
    · rw [hseg.2.1]
      exact padded_noHoles _ _

noncomputable def inputSymbol (tm : FinTM2) (x : tm.Γ tm.k₀) : Symbol tm tm.k₀ := by
  classical
  letI := tm.ΛFin
  letI := tm.σFin
  letI := tm.Γk₀Fin
  exact ⟨x, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)⟩

theorem inputSymbol_injective (tm : FinTM2) : Function.Injective (inputSymbol tm) := by
  intro x y h
  exact congrArg Subtype.val h

noncomputable def inputCells (tm : FinTM2) (M : ℕ) (r : Row tm M) : List (Option (Symbol tm tm.k₀)) :=
  List.ofFn (r.cells tm.k₀)

def CertificateBoundary {C : Type*} (tm : FinTM2) (M : ℕ) (e : C → Symbol tm tm.k₀)
    (header : List (Symbol tm tm.k₀)) (B : ℕ) (r : Row tm M) : Prop :=
  r.control = (some tm.main, tm.initialState) ∧
  HasCertificate e header B M (inputCells tm M r) ∧
  ∀ k, k ≠ tm.k₀ → ∀ n, r.cells k n = none

end ProteinFolding.SAT.CookLevinCertificateCells
