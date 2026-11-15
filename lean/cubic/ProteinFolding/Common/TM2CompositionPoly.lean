import ProteinFolding.Common.TM2Composition
import ProteinFolding.Common.TM2PolynomialTime

/-! Packaging the concrete sequential TM2 construction into the frozen
polynomial-time interface. Empty intermediate alphabets are handled explicitly.
No machine-composition hypothesis is an input to the resulting construction. -/

namespace ProteinFolding.TM2CompositionPoly

open Computability Turing

noncomputable def alphabetSeed (Alphabet : Type) : Option Alphabet := by
  classical
  exact if h : Nonempty Alphabet then some (Classical.choice h) else none

theorem alphabetSeed_none (Alphabet : Type) (h : alphabetSeed Alphabet = none) :
    IsEmpty Alphabet := by
  classical
  refine ⟨fun a => ?_⟩
  have hn : Nonempty Alphabet := ⟨a⟩
  simp [alphabetSeed, hn] at h

variable {A B D : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {ed : FinEncoding D} {f : A → B} {g : B → D}

def bridge (hf : TM2ComputableInPolyTime ea eb f)
    (hg : TM2ComputableInPolyTime eb ed g) : hf.tm.Γ hf.tm.k₁ ≃ hg.tm.Γ hg.tm.k₀ :=
  hf.outputAlphabet.trans hg.inputAlphabet.symm

noncomputable def auxiliary (hf : TM2ComputableInPolyTime ea eb f)
    (hg : TM2ComputableInPolyTime eb ed g) : TM2ComputableAux ea.Γ ed.Γ where
  tm := TM2Composition.machine hf.tm hg.tm (bridge hf hg)
    (alphabetSeed (hf.tm.Γ hf.tm.k₁))
  inputAlphabet := hf.inputAlphabet
  outputAlphabet := hg.outputAlphabet

theorem bridge_word (hf : TM2ComputableInPolyTime ea eb f)
    (hg : TM2ComputableInPolyTime eb ed g) (w : List eb.Γ) :
    (w.map hf.outputAlphabet.symm).map (bridge hf hg) = w.map hg.inputAlphabet.symm := by
  simp [bridge, List.map_map, Function.comp_def]

noncomputable def compose (hf : TM2ComputableInPolyTime ea eb f)
    (hg : TM2ComputableInPolyTime eb ed g) : TM2ComputableInPolyTime ea ed (g ∘ f) :=
  TM2PolynomialTime.assembleComposition hf hg (auxiliary hf hg) (by
    intro a
    have hA := hf.outputsFun a
    have hB := hg.outputsFun (f a)
    change TM2OutputsInTime hg.tm
      ((eb.encode (f a)).map hg.inputAlphabet.symm)
      (some ((ed.encode (g (f a))).map hg.outputAlphabet.symm)) _ at hB
    rw [← bridge_word hf hg (eb.encode (f a))] at hB
    have hrun := TM2Composition.machine_outputsInTime hf.tm hg.tm
      (bridge hf hg) (alphabetSeed (hf.tm.Γ hf.tm.k₁))
      (alphabetSeed_none (hf.tm.Γ hf.tm.k₁)) _ _ _ _ _ hA hB
    simpa only [auxiliary, List.length_map] using hrun)

end ProteinFolding.TM2CompositionPoly
