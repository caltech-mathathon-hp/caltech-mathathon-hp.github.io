import ProteinFolding.Common.CookLevinProofPaddedWindow
import Mathlib.Data.Fintype.Sigma

/-! Concrete Boolean rows for the finite-symbol TM2 tableau. The number of
bits is linear in the stack bound. Window and query auxiliaries use types
whose sizes depend only on the fixed machine. One-hot component constraints
characterize exactly the encoded typed rows, including malformed-code rejection.
-/

namespace ProteinFolding.SAT.CookLevinRows

open Turing TM2 CookLevinAlphabet CookLevinWindow CookLevinWindowCNF
open CookLevinCells CookLevinPaddedWindow CookLevinLocal CookLevinCircuit

structure Row (tm : FinTM2) (M : ℕ) where
  control : Control tm
  cells : ∀ k, Fin M → Option (Symbol tm k)
  window : PaddedWindow tm
  replacement : Replacement tm
  queries : ∀ k, Fin M → CellWindow tm k

def Bit (tm : FinTM2) (M : ℕ) :=
  Control tm ⊕ (Σ k, Fin M × Option (Symbol tm k)) ⊕
    PaddedWindow tm ⊕ Replacement tm ⊕ (Σ k, Fin M × CellWindow tm k)

noncomputable instance bitFintype (tm : FinTM2) (M : ℕ) : Fintype (Bit tm M) := by
  letI := tm.kFin
  unfold Bit
  infer_instance

open scoped Classical in
noncomputable def encodeRow {tm : FinTM2} {M : ℕ} (r : Row tm M) : Bit tm M → Bool
  | .inl c => decide (c = r.control)
  | .inr (.inl ⟨k, n, b⟩) => @decide (b = r.cells k n) (Classical.propDecidable _)
  | .inr (.inr (.inl w)) => decide (w = r.window)
  | .inr (.inr (.inr (.inl s))) => decide (s = r.replacement)
  | .inr (.inr (.inr (.inr ⟨k, n, q⟩))) => decide (q = r.queries k n)

def controlTag (tm : FinTM2) (M : ℕ) (c : Control tm) : Bit tm M := .inl c
def cellTag (tm : FinTM2) (M : ℕ) (k : tm.K) (n : Fin M) (b : Option (Symbol tm k)) : Bit tm M :=
  .inr (.inl ⟨k, n, b⟩)
def windowTag (tm : FinTM2) (M : ℕ) (w : PaddedWindow tm) : Bit tm M := .inr (.inr (.inl w))
def replacementTag (tm : FinTM2) (M : ℕ) (r : Replacement tm) : Bit tm M :=
  .inr (.inr (.inr (.inl r)))
def queryTag (tm : FinTM2) (M : ℕ) (k : tm.K) (n : Fin M) (q : CellWindow tm k) : Bit tm M :=
  .inr (.inr (.inr (.inr ⟨k, n, q⟩)))

noncomputable def codeSlots {A B : Type*} [Fintype A] (tag : A → B) : List B :=
  Finset.univ.toList.map tag

theorem codeSlots_length {A B : Type*} [Fintype A] (tag : A → B) :
    (codeSlots tag).length = Fintype.card A := by simp [codeSlots]

open scoped Classical in
theorem codeSlots_match_iff {A B : Type*} [Fintype A] (tag : A → B) (a : B → Bool) (v : A) :
    (codeSlots tag).map a = finiteCode v ↔ ∀ x, a (tag x) = decide (x = v) := by
  classical
  unfold codeSlots finiteCode
  rw [List.map_map, List.map_inj_left]
  simp only [Finset.mem_toList, Finset.mem_univ, forall_const, Function.comp_apply]

noncomputable def codeAllowed (A : Type*) [Fintype A] (bs : List Bool) : Bool := by
  classical
  exact decide (∃ v : A, bs = finiteCode v)

theorem codeAllowed_iff (A : Type*) [Fintype A] (bs : List Bool) :
    codeAllowed A bs = true ↔ ∃ v : A, bs = finiteCode v := by
  classical
  simp only [codeAllowed, decide_eq_true_eq]

def Valid (tm : FinTM2) (M : ℕ) (a : Bit tm M → Bool) : Prop :=
  codeAllowed (Control tm) ((codeSlots (controlTag tm M)).map a) = true ∧
  codeAllowed (PaddedWindow tm) ((codeSlots (windowTag tm M)).map a) = true ∧
  codeAllowed (Replacement tm) ((codeSlots (replacementTag tm M)).map a) = true ∧
  (∀ k n, codeAllowed (Option (Symbol tm k)) ((codeSlots (cellTag tm M k n)).map a) = true) ∧
  (∀ k n, codeAllowed (CellWindow tm k) ((codeSlots (queryTag tm M k n)).map a) = true)

theorem valid_iff (tm : FinTM2) (M : ℕ) (a : Bit tm M → Bool) :
    Valid tm M a ↔ ∃ r : Row tm M, a = encodeRow r := by
  classical
  constructor
  · rintro ⟨hc, hw, hr, hb, hq⟩
    obtain ⟨c, hc⟩ := (codeAllowed_iff _ _).mp hc
    obtain ⟨w, hw⟩ := (codeAllowed_iff _ _).mp hw
    obtain ⟨r, hr⟩ := (codeAllowed_iff _ _).mp hr
    have hbs : ∀ k n, ∃ b, (codeSlots (cellTag tm M k n)).map a = finiteCode b :=
      fun k n => (codeAllowed_iff (Option (Symbol tm k)) _).mp (hb k n)
    have hqs : ∀ k n, ∃ q, (codeSlots (queryTag tm M k n)).map a = finiteCode q :=
      fun k n => (codeAllowed_iff (CellWindow tm k) _).mp (hq k n)
    choose cells hcells using hbs
    choose queries hqueries using hqs
    refine ⟨⟨c, cells, w, r, queries⟩, ?_⟩
    funext bit
    rcases bit with c' | ⟨k, n, b⟩ | w' | r' | ⟨k, n, q⟩
    · exact (codeSlots_match_iff _ _ _).mp hc c'
    · simpa only [cellTag, encodeRow] using (codeSlots_match_iff _ _ _).mp (hcells k n) b
    · exact (codeSlots_match_iff _ _ _).mp hw w'
    · exact (codeSlots_match_iff _ _ _).mp hr r'
    · exact (codeSlots_match_iff _ _ _).mp (hqueries k n) q
  · rintro ⟨r, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply (codeAllowed_iff _ _).mpr
      exact ⟨r.control, (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)⟩
    · apply (codeAllowed_iff _ _).mpr
      exact ⟨r.window, (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)⟩
    · apply (codeAllowed_iff _ _).mpr
      exact ⟨r.replacement, (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)⟩
    · intro k n
      apply (codeAllowed_iff _ _).mpr
      exact ⟨r.cells k n, (codeSlots_match_iff _ _ _).mpr (fun _ => by simp only [cellTag, encodeRow])⟩
    · intro k n
      apply (codeAllowed_iff _ _).mpr
      exact ⟨r.queries k n, (codeSlots_match_iff _ _ _).mpr (fun _ => rfl)⟩

noncomputable def width (tm : FinTM2) (M : ℕ) : ℕ := Fintype.card (Bit tm M)

theorem width_pos (tm : FinTM2) (M : ℕ) : 0 < width tm M := by
  letI : Nonempty (Bit tm M) := ⟨controlTag tm M (none, tm.initialState)⟩
  exact Fintype.card_pos

noncomputable def bitIndex (tm : FinTM2) (M : ℕ) : Bit tm M ≃ Fin (width tm M) := Fintype.equivFin _

noncomputable def componentConstraint {A : Type*} [Fintype A]
    (tm : FinTM2) (M : ℕ) (tag : A → Bit tm M) : Constraint :=
  ⟨(codeSlots tag).map (fun b => (bitIndex tm M b).val), codeAllowed A⟩

theorem componentConstraint_iff {A : Type*} [Fintype A]
    (tm : FinTM2) (M : ℕ) (tag : A → Bit tm M) (a : ℕ → Bool) :
    (componentConstraint tm M tag).Holds a ↔
      codeAllowed A ((codeSlots tag).map (fun b => a (bitIndex tm M b).val)) = true := by
  simp only [componentConstraint, Constraint.Holds, List.map_map, Function.comp_def]

noncomputable def validityConstraints (tm : FinTM2) (M : ℕ) : List Constraint := by
  letI := tm.kFin
  exact [componentConstraint tm M (controlTag tm M),
    componentConstraint tm M (windowTag tm M), componentConstraint tm M (replacementTag tm M)] ++
    Finset.univ.toList.flatMap (fun k => (List.finRange M).flatMap (fun n =>
      [componentConstraint tm M (cellTag tm M k n), componentConstraint tm M (queryTag tm M k n)]))

theorem validityConstraints_iff (tm : FinTM2) (M : ℕ) (a : ℕ → Bool) :
    Satisfied a (compileConstraints (validityConstraints tm M)) ↔
      ∃ r : Row tm M, (fun b => a (bitIndex tm M b).val) = encodeRow r := by
  letI := tm.kFin
  rw [compileConstraints_iff, ← valid_iff]
  unfold validityConstraints Valid
  simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap,
    List.not_mem_nil, false_implies, forall_const,
    Finset.mem_toList, Finset.mem_univ, List.mem_finRange,
    componentConstraint_iff, and_assoc, forall_and]
  simp

def cellIndexEquiv (tm : FinTM2) (M : ℕ) :
    (Σ k, Fin M × Option (Symbol tm k)) ≃ Fin M × (Σ k, Option (Symbol tm k)) where
  toFun x := (x.2.1, ⟨x.1, x.2.2⟩)
  invFun x := ⟨x.2.1, x.1, x.2.2⟩
  left_inv := by rintro ⟨k, n, b⟩; rfl
  right_inv := by rintro ⟨n, k, b⟩; rfl

def queryIndexEquiv (tm : FinTM2) (M : ℕ) :
    (Σ k, Fin M × CellWindow tm k) ≃ Fin M × (Σ k, CellWindow tm k) where
  toFun x := (x.2.1, ⟨x.1, x.2.2⟩)
  invFun x := ⟨x.2.1, x.1, x.2.2⟩
  left_inv := by rintro ⟨k, n, b⟩; rfl
  right_inv := by rintro ⟨n, k, b⟩; rfl

noncomputable def widthBase (tm : FinTM2) : ℕ :=
  Fintype.card (Control tm) + Fintype.card (PaddedWindow tm) + Fintype.card (Replacement tm)

noncomputable def widthSlope (tm : FinTM2) : ℕ := by
  letI := tm.kFin
  exact Fintype.card (Σ k, Option (Symbol tm k)) + Fintype.card (Σ k, CellWindow tm k)

/-- Exact linear row size, including every auxiliary bit. -/
theorem width_linear (tm : FinTM2) (M : ℕ) :
    width tm M = widthBase tm + M * widthSlope tm := by
  letI := tm.kFin
  simp only [width, Bit, Fintype.card_sum]
  rw [Fintype.card_congr (cellIndexEquiv tm M), Fintype.card_prod,
    Fintype.card_congr (queryIndexEquiv tm M), Fintype.card_prod]
  simp only [Fintype.card_fin, widthBase, widthSlope, Nat.mul_add]
  omega

theorem width_polynomial (tm : FinTM2) :
    ∃ p : Polynomial ℕ, ∀ M, width tm M = p.eval M := by
  refine ⟨Polynomial.C (widthBase tm) + Polynomial.X * Polynomial.C (widthSlope tm), ?_⟩
  intro M
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] using width_linear tm M

end ProteinFolding.SAT.CookLevinRows
