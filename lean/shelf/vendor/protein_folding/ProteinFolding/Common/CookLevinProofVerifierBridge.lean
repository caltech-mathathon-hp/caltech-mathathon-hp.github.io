import ProteinFolding.Common.CookLevinProofCertificateBoundary
import ProteinFolding.Common.CookLevinProofPadded
import ProteinFolding.Common.TM2PolynomialTime

/-! Extract the exact bounded-word verifier semantics from the unchanged InNP
definition. Arbitrary finite certificate alphabets and the required encoder
surjectivity are retained. The actual verifier machine is run for one uniform
polynomial horizon rather than for a certificate-dependent number of steps.
-/

namespace ProteinFolding.SAT.CookLevinVerifierBridge

open Computability Turing TM2 CookLevinPadded CookLevinCertificateBoundary

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

def inputHeader (x : A) : List (h.tm.Γ h.tm.k₀) :=
  (ea.encode x).map (fun a => h.inputAlphabet.symm (.left a)) ++ [h.inputAlphabet.symm .sep]

def certificateLetter (b : ec.Γ) : h.tm.Γ h.tm.k₀ := h.inputAlphabet.symm (.right b)

def verifierInput (x : A) (w : List ec.Γ) : List (h.tm.Γ h.tm.k₀) :=
  inputHeader h x ++ w.map (certificateLetter h)

theorem verifierInput_encoded (x : A) (c : C) :
    verifierInput h x (ec.encode c) = ((pairEncoding ea ec).encode (x, c)).map h.inputAlphabet.symm := by
  simp [verifierInput, inputHeader, certificateLetter, pairEncoding, List.map_append,
    List.map_map, Function.comp_def]

def acceptedConfig : h.tm.Cfg := haltList h.tm [h.outputAlphabet.symm true]

noncomputable def uniformTime (p : Polynomial ℕ) (x : A) : ℕ :=
  h.time.eval ((ea.encode x).length + p.eval (ea.encode x).length + 1)

theorem haltList_injective (tm : FinTM2) : Function.Injective (haltList tm) := by
  intro u v huv
  have hs := congrArg (fun c : tm.Cfg => c.stk tm.k₁) huv
  simpa only [haltList, dif_pos rfl] using hs

/-- Every bounded encoded certificate can use the same polynomial horizon.
Acceptance is exactly the original Boolean verifier value, including early halt. -/
theorem verifier_padded_iff (p : Polynomial ℕ) (x : A) (c : C)
    (hc : (ec.encode c).length ≤ p.eval (ea.encode x).length) :
    (paddedStep h.tm)^[uniformTime h p x] (initList h.tm (verifierInput h x (ec.encode c))) = acceptedConfig h ↔
      f (x, c) = true := by
  have hlen : ((pairEncoding ea ec).encode (x, c)).length ≤
      (ea.encode x).length + p.eval (ea.encode x).length + 1 := by
    simp only [pairEncoding, List.length_append, List.length_map, List.length_cons]
    omega
  have ht := TM2PolynomialTime.eval_monotone h.time hlen
  have hout := h.outputsFun (x, c)
  let hu : TM2OutputsInTime h.tm
      (((pairEncoding ea ec).encode (x, c)).map h.inputAlphabet.symm)
      (some ((finEncodingBoolBool.encode (f (x, c))).map h.outputAlphabet.symm)) (uniformTime h p x) :=
    { hout with steps_le_m := hout.steps_le_m.trans ht }
  have hr := outputsInTime_paddedRun h.tm _ _ (uniformTime h p x) hu
  rw [verifierInput_encoded, hr]
  constructor
  · intro he
    have ho := haltList_injective h.tm he
    have hb : [h.outputAlphabet.symm (f (x, c))] = [h.outputAlphabet.symm true] := by
      simpa only [finEncodingBoolBool, encodeBool, List.map_cons, List.map_nil] using ho
    exact h.outputAlphabet.symm.injective (List.singleton_inj.mp hb)
  · intro hf
    simp only [hf, finEncodingBoolBool, encodeBool, acceptedConfig]
    rfl

theorem verifier_words_iff (p : Polynomial ℕ) (hs : Function.Surjective ec.encode) (x : A) :
    (∃ c : C, (ec.encode c).length ≤ p.eval (ea.encode x).length ∧ f (x, c) = true) ↔
      ∃ w : List ec.Γ, w.length ≤ p.eval (ea.encode x).length ∧
        (paddedStep h.tm)^[uniformTime h p x] (initList h.tm (verifierInput h x w)) = acceptedConfig h := by
  constructor
  · rintro ⟨c, hc, hf⟩
    exact ⟨ec.encode c, hc, (verifier_padded_iff h p x c hc).mpr hf⟩
  · rintro ⟨w, hw, hr⟩
    obtain ⟨c, rfl⟩ := hs w
    exact ⟨c, hw, (verifier_padded_iff h p x c hw).mp hr⟩

theorem inNP_word_verifier {A : Type} (ea : FinEncoding A) (L : A → Prop) (hnp : InNP ea L) :
    ∃ (C : Type) (ec : FinEncoding C) (p : Polynomial ℕ) (f : A × C → Bool)
      (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f),
      Function.Surjective ec.encode ∧ ∀ x,
        L x ↔ ∃ w : List ec.Γ, w.length ≤ p.eval (ea.encode x).length ∧
          (paddedStep h.tm)^[uniformTime h p x] (initList h.tm (verifierInput h x w)) = acceptedConfig h := by
  obtain ⟨C, ec, hs, p, R, ⟨f, ⟨h⟩, hf⟩, hL⟩ := hnp
  refine ⟨C, ec, p, f, h, hs, ?_⟩
  intro x
  rw [hL x, ← verifier_words_iff h p hs x]
  constructor
  · rintro ⟨c, hc, hR⟩
    exact ⟨c, hc, (hf (x, c)).mpr hR⟩
  · rintro ⟨c, hc, hR⟩
    exact ⟨c, hc, (hf (x, c)).mp hR⟩

end ProteinFolding.SAT.CookLevinVerifierBridge
