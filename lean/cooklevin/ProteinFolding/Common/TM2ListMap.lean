import ProteinFolding.Common.TM2ListMapBounds
import ProteinFolding.Common.TM2Constants
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2WordMap

/-! Polynomial-time parameterized list mapping by an actual finite TM2.
The child function is run on each record with the same encoded parameter;
its output words are concatenated in source order. Every transfer, child
simulation, auxiliary-stack cleanup and final-state reset is accounted for.
No nonempty-alphabet assumption is imposed by the public constructor. -/

namespace ProteinFolding.TM2ListMap

open Computability Turing TM2 TM2CompositionPoly TM2ProductMap

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

def mappedFunction (f : P × A → List B) (px : P × List A) : List B :=
  px.2.flatMap (fun a => f (px.1, a))

section Inhabited
variable [Inhabited B]

noncomputable def machine : FinTM2 := by
  letI := h.tm.kFin
  letI := h.tm.ΛFin
  letI := h.tm.σFin
  letI := h.tm.Γk₀Fin
  letI := ep.ΓFin
  letI := ea.ΓFin
  letI : Fintype (OutLetter h) := Fintype.ofEquiv B h.outputAlphabet.symm
  exact
    { K := Stack h
      k₀ := .inr .input
      k₁ := .inr .output
      Γ := Alphabet h
      Λ := Phase h
      main := .parameter
      σ := State h
      initialState := initial h
      Γk₀Fin := inferInstanceAs (Fintype (RawSymbol (ep := ep) (ea := ea)))
      m := program h }

theorem initList_eq (w : List (RawSymbol (ep := ep) (ea := ea))) :
    initList (machine h) w = cfg h .parameter (initial h) (emptyChild h) w [] [] [] [] [] := by
  apply congrArg (fun S => (⟨some .parameter, initial h, S⟩ : Cfg (Alphabet h) (Phase h) (State h)))
  funext k
  cases k with
  | inl k => simp [machine, contents, TM2Embedding.joinStacks, emptyChild]
  | inr k => cases k <;> simp [machine, contents, TM2Embedding.joinStacks, extraContents]

theorem haltList_eq (out : List B) : haltList (machine h) out = halted h out := by
  apply congrArg (fun S => (⟨none, initial h, S⟩ : Cfg (Alphabet h) (Phase h) (State h)))
  funext k
  cases k with
  | inl k => simp [machine, contents, TM2Embedding.joinStacks, emptyChild]
  | inr k => cases k <;> simp [machine, contents, TM2Embedding.joinStacks, extraContents]

noncomputable def machine_outputs (p : P) (xs : List A) :
    TM2OutputsInTime (machine h) (inputWord (ep := ep) (ea := ea) p xs)
      (some (flatOutput (f := f) p xs))
      ((mappingTime h).eval (inputWord (ep := ep) (ea := ea) p xs).length) := by
  refine
    { steps := runningTime h p xs
      evals_in_steps := ?_
      steps_le_m := runningTime_bound h p xs }
  · change run h _ (initList (machine h) _) = some (haltList (machine h) _)
    rw [initList_eq, haltList_eq]
    exact program_run h p xs

noncomputable def inhabitedComputable :
    TM2ComputableInPolyTime (pairEncoding ep (listEncoding ea)) (wordEncoding B) (mappedFunction f) where
  tm := machine h
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := mappingTime h
  outputsFun px := by
    obtain ⟨p, xs⟩ := px
    change TM2OutputsInTime (machine h)
      (List.map id ((pairEncoding ep (listEncoding ea)).encode (p, xs)))
      (some (List.map id (flatOutput (f := f) p xs)))
      ((mappingTime h).eval ((pairEncoding ep (listEncoding ea)).encode (p, xs)).length)
    rw [encoding_word]
    simpa only [List.map_id] using machine_outputs h p xs

end Inhabited

/-- Run a polynomial-time word-valued child on each encoded record, retaining
the common parameter. The returned witness is an actual finite TM2 with a
polynomial bound derived from the child time and its output-size polynomial. -/
noncomputable def flatMapComputable :
    TM2ComputableInPolyTime (pairEncoding ep (listEncoding ea)) (wordEncoding B) (mappedFunction f) := by
  classical
  by_cases hb : Nonempty B
  · letI : Inhabited B := ⟨Classical.choice hb⟩
    exact inhabitedComputable h
  · have he (w : List B) : w = [] := by
      cases w with
      | nil => rfl
      | cons b w => exact False.elim (hb ⟨b⟩)
    have hf : mappedFunction f = fun _ => [] := by
      funext px
      exact he _
    rw [hf]
    exact TM2Constants.constantComputable _ (wordEncoding B) []

section TypedMap

variable {C : Type} (ec : FinEncoding C) {g : P × A → C}

noncomputable def encodedBlockComputable
    (hg : TM2ComputableInPolyTime (pairEncoding ep ea) ec g) :
    TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding (Option ec.Γ))
      (fun pa => (ec.encode (g pa)).map some ++ [none]) := by
  let hc : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding ec.Γ)
      (fun pa => ec.encode (g pa)) :=
    { toTM2ComputableAux := hg.toTM2ComputableAux
      time := hg.time
      outputsFun := hg.outputsFun }
  let hs := compose hc (TM2WordMap.mapComputable (some : ec.Γ → Option ec.Γ))
  let hn := TM2Constants.constantComputable (pairEncoding ep ea) (wordEncoding (Option ec.Γ)) [none]
  exact compose (pairComputable hs hn) (TM2PairProjections.concatComputable (Option ec.Γ))

theorem encoded_map (p : P) (xs : List A) :
    mappedFunction (fun pa => (ec.encode (g pa)).map some ++ [none]) (p, xs) =
      (listEncoding ec).encode (xs.map (fun a => g (p, a))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa [mappedFunction, listEncoding, encodeFields, List.append_assoc] using
      congrArg ((ec.encode (g (p, a))).map some ++ none :: ·) ih

/-- Polynomial-time typed list mapping, preserving the shared parameter and
using the explicit terminator encoding on both input and output lists. -/
noncomputable def mapComputable (hg : TM2ComputableInPolyTime (pairEncoding ep ea) ec g) :
    TM2ComputableInPolyTime (pairEncoding ep (listEncoding ea)) (listEncoding ec)
      (fun px => px.2.map (fun a => g (px.1, a))) := by
  let hb := encodedBlockComputable ec hg
  let hm := flatMapComputable hb
  exact
    { toTM2ComputableAux := hm.toTM2ComputableAux
      time := hm.time
      outputsFun := fun px => by
        obtain ⟨p, xs⟩ := px
        have hout := hm.outputsFun (p, xs)
        simpa only [wordEncoding, id_eq, encoded_map (ec := ec) (g := g)] using hout }

end TypedMap

end ProteinFolding.TM2ListMap
