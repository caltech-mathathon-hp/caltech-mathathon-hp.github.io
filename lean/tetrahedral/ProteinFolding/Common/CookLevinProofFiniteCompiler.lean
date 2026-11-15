import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.TM2EncodingWords
import ProteinFolding.Common.TM2WordEquality

/-! Actual finite-table compilation between arbitrary finite encodings.
Encoded equality is checked by the concrete word-comparison machine. Finite
case selection uses checked conditional/composition machines, so machine-fixed
truth tables and alphabet translations require no computability assumptions.
-/

namespace ProteinFolding.SAT.CookLevinFiniteCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap

theorem encode_injective {A : Type} (ea : FinEncoding A) : Function.Injective ea.encode := by
  intro x y h
  have hd := congrArg ea.decode h
  rw [ea.decode_encode, ea.decode_encode] at hd
  exact Option.some.inj hd

open scoped Classical in
noncomputable def fixedEqualityComputable {A : Type} (ea : FinEncoding A) (v : A) :
    TM2ComputableInPolyTime ea finEncodingBoolBool (fun x => decide (x = v)) := by
  classical
  letI := ea.ΓFin
  let hc := pairComputable (TM2EncodingWords.encodeComputable ea)
    (TM2Constants.constantComputable ea (wordEncoding ea.Γ) (ea.encode v))
  let hm := compose hc (TM2WordEquality.wordEqualityComputable ea.Γ)
  have he : (fun x => decide (ea.encode x = ea.encode v)) = (fun x => decide (x = v)) := by
    funext x
    simp only [(encode_injective ea).eq_iff]
  rw [← he]
  exact hm

theorem finitePatch {A B : Type} (ea : FinEncoding A) (eb : FinEncoding B)
    (f : A → B) (b : B) (s : Finset A) :
    ∃ g : A → B, Nonempty (TM2ComputableInPolyTime ea eb g) ∧ ∀ x ∈ s, g x = f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => b, ⟨TM2Constants.constantComputable ea eb b⟩, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨g, ⟨hg⟩, hgf⟩ := ih
    let g' : A → B := fun x => if x = a then f a else g x
    have hcode : Nonempty (TM2ComputableInPolyTime ea eb g') := by
      have hm := TM2Conditional.iteComputable (fixedEqualityComputable ea a)
        (TM2Constants.constantComputable ea eb (f a)) hg
      have he : (fun x => if decide (x = a) then f a else g x) = g' := by
        funext x
        by_cases hx : x = a <;> simp [g', hx]
      rw [← he]
      exact ⟨hm⟩
    refine ⟨g', hcode, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [g']
    · by_cases hxa : x = a
      · subst x; simp [g']
      · simp only [g', if_neg hxa]
        exact hgf x hx

/-- Compile any fixed finite-domain table into a genuine polynomial TM2,
including empty source types and empty encoding alphabets. -/
noncomputable def finiteFunctionComputable {A B : Type} [Fintype A]
    (ea : FinEncoding A) (eb : FinEncoding B) (f : A → B) :
    TM2ComputableInPolyTime ea eb f := by
  classical
  by_cases ha : Nonempty A
  · have hm : Nonempty (TM2ComputableInPolyTime ea eb f) := by
      obtain ⟨g, ⟨hg⟩, hgf⟩ := finitePatch ea eb f (f (Classical.choice ha)) Finset.univ
      have he : g = f := funext (fun x => hgf x (Finset.mem_univ x))
      rw [← he]
      exact ⟨hg⟩
    exact Classical.choice hm
  · letI := ea.ΓFin
    exact
      { tm := TM2Constants.machine ea.Γ ([] : List eb.Γ)
        inputAlphabet := Equiv.refl _
        outputAlphabet := Equiv.refl _
        time := Polynomial.X + Polynomial.C 2
        outputsFun x := False.elim (ha ⟨x⟩) }

end ProteinFolding.SAT.CookLevinFiniteCompiler
