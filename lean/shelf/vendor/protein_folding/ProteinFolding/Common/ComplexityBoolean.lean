import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2Boolean

/-! Boolean closure for the frozen deterministic polynomial-time predicates.
Both predicates are physically computed by the independent pairing machine;
the finite Boolean machine then combines their output bits. -/

namespace ProteinFolding

open Computability Turing

variable {A B : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {P Q : A → Prop} {R : B → Prop} {f : A → B}

theorem polyTimeDecidable_and (hP : PolyTimeDecidable ea P) (hQ : PolyTimeDecidable ea Q) :
    PolyTimeDecidable ea (fun x => P x ∧ Q x) := by
  obtain ⟨p, ⟨hp⟩, hpc⟩ := hP
  obtain ⟨q, ⟨hq⟩, hqc⟩ := hQ
  refine ⟨fun x => p x && q x,
    ⟨TM2CompositionPoly.compose (TM2ProductMap.pairComputable hp hq) TM2Boolean.andComputable⟩, ?_⟩
  intro x
  simp only [Bool.and_eq_true, hpc x, hqc x]

theorem polyTimeDecidable_or (hP : PolyTimeDecidable ea P) (hQ : PolyTimeDecidable ea Q) :
    PolyTimeDecidable ea (fun x => P x ∨ Q x) := by
  obtain ⟨p, ⟨hp⟩, hpc⟩ := hP
  obtain ⟨q, ⟨hq⟩, hqc⟩ := hQ
  refine ⟨fun x => p x || q x,
    ⟨TM2CompositionPoly.compose (TM2ProductMap.pairComputable hp hq)
      (TM2Boolean.binaryComputable Bool.or)⟩, ?_⟩
  intro x
  simp only [Bool.or_eq_true, hpc x, hqc x]

theorem polyTimeDecidable_not (hP : PolyTimeDecidable ea P) :
    PolyTimeDecidable ea (fun x => ¬ P x) := by
  obtain ⟨p, ⟨hp⟩, hpc⟩ := hP
  refine ⟨fun x => !(p x), ⟨TM2CompositionPoly.compose hp TM2Boolean.notComputable⟩, ?_⟩
  intro x
  have hx := hpc x
  cases hpx : p x <;> simp_all

theorem polyTimeDecidable_precomp (hf : TM2ComputableInPolyTime ea eb f)
    (hR : PolyTimeDecidable eb R) : PolyTimeDecidable ea (fun x => R (f x)) := by
  obtain ⟨r, ⟨hr⟩, hrc⟩ := hR
  exact ⟨r ∘ f, ⟨TM2CompositionPoly.compose hf hr⟩, fun x => hrc (f x)⟩

/-- Package a sound word verifier and its polynomial completeness bound into
the frozen NP definition. All words remain represented by identity encoding. -/
theorem inNP_of_word_verifier (L : A → Prop) (p : Polynomial ℕ)
    (V : A × List Bool → Prop)
    (hV : PolyTimeDecidable (pairEncoding ea (wordEncoding Bool)) V)
    (hsound : ∀ x w, V (x, w) → L x)
    (hcomplete : ∀ x, L x → ∃ w, w.length ≤ p.eval (ea.encode x).length ∧ V (x, w)) :
    InNP ea L := by
  refine ⟨List Bool, wordEncoding Bool, fun w => ⟨w, rfl⟩, p, V, hV, ?_⟩
  intro x
  constructor
  · intro hx
    exact hcomplete x hx
  · rintro ⟨w, _, hw⟩
    exact hsound x w hw

end ProteinFolding
