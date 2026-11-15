import ProteinFolding.Common.CookLevinProofFiniteCompiler
import ProteinFolding.Common.CookLevinProofMapCompiler

/-! Actual finite selection among polynomial child machines on a common
variable parameter, and fixed finite sequences of CNF/word emitters. This is
the template compiler used for the machine-fixed local transition tables.
-/

namespace ProteinFolding.SAT.CookLevinFiniteFamilyCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinFiniteCompiler CookLevinMapCompiler

def symbolEncoding (I : Type) [Fintype I] : FinEncoding I where
  Γ := I
  ΓFin := inferInstance
  encode i := [i]
  decode := List.head?
  decode_encode _ := rfl

theorem familyPatch {X I Y : Type} (ex : FinEncoding X) (ei : FinEncoding I) (ey : FinEncoding Y)
    (f : I → X → Y) (h : ∀ i, TM2ComputableInPolyTime ex ey (f i))
    (initial : I) (s : Finset I) :
    ∃ g : X × I → Y, Nonempty (TM2ComputableInPolyTime (pairEncoding ex ei) ey g) ∧
      ∀ i ∈ s, ∀ x, g (x, i) = f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun p => f initial p.1,
      ⟨compose (TM2PairProjections.fstComputable ex ei) (h initial)⟩, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g, ⟨hg⟩, hgf⟩ := ih
    let g' : X × I → Y := fun p => if p.2 = i then f i p.1 else g p
    have hm : Nonempty (TM2ComputableInPolyTime (pairEncoding ex ei) ey g') := by
      let hp := compose (TM2PairProjections.sndComputable ex ei) (fixedEqualityComputable ei i)
      let hf := compose (TM2PairProjections.fstComputable ex ei) (h i)
      let hc := TM2Conditional.iteComputable hp hf hg
      have he : (fun p : X × I => if decide (p.2 = i) then f i p.1 else g p) = g' := by
        funext p
        by_cases heq : p.2 = i <;> simp [g', heq]
      rw [← he]
      exact ⟨hc⟩
    refine ⟨g', hm, ?_⟩
    intro j hj x
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp [g']
    · by_cases hji : j = i
      · subst j; simp [g']
      · simpa only [g', if_neg hji] using hgf j hj x

noncomputable def finiteFamilyComputable {X I Y : Type} [Fintype I]
    (ex : FinEncoding X) (ei : FinEncoding I) (ey : FinEncoding Y)
    (f : I → X → Y) (h : ∀ i, TM2ComputableInPolyTime ex ey (f i)) :
    TM2ComputableInPolyTime (pairEncoding ex ei) ey (fun p : X × I => f p.2 p.1) := by
  classical
  by_cases hi : Nonempty I
  · have hm : Nonempty (TM2ComputableInPolyTime (pairEncoding ex ei) ey (fun p : X × I => f p.2 p.1)) := by
      obtain ⟨g, ⟨hg⟩, hgf⟩ := familyPatch ex ei ey f h (Classical.choice hi) Finset.univ
      have he : g = (fun p : X × I => f p.2 p.1) := funext (fun p => hgf p.2 (Finset.mem_univ _) p.1)
      rw [← he]
      exact ⟨hg⟩
    exact Classical.choice hm
  · letI := (pairEncoding ex ei).ΓFin
    exact
      { tm := TM2Constants.machine (pairEncoding ex ei).Γ ([] : List ey.Γ)
        inputAlphabet := Equiv.refl _
        outputAlphabet := Equiv.refl _
        time := Polynomial.X + Polynomial.C 2
        outputsFun p := False.elim (hi ⟨p.2⟩) }

noncomputable def fixedWordSequenceCompiler {X : Type} {ex : FinEncoding X} (q : ℕ)
    (f : Fin q → X → List Sym) (h : ∀ i, TM2ComputableInPolyTime ex (wordEncoding Sym) (f i)) :
    TM2ComputableInPolyTime ex (wordEncoding Sym)
      (fun x => (List.finRange q).flatMap (fun i => f i x)) := by
  let hc := finiteFamilyComputable ex (symbolEncoding (Fin q)) (wordEncoding Sym) f h
  let hl := TM2ListMap.flatMapComputable hc
  let hp := pairComputable (idComputableInPolyTime ex)
    (TM2Constants.constantComputable ex (TM2ListMap.listEncoding (symbolEncoding (Fin q))) (List.finRange q))
  exact compose (f := fun x : X => (x, List.finRange q))
    (g := fun p : X × List (Fin q) => p.2.flatMap (fun i => f i p.1)) hp hl

noncomputable def fixedCNFSequenceCompiler {X : Type} {ex : FinEncoding X} (q : ℕ)
    (f : Fin q → X → CNF) (h : ∀ i, TM2ComputableInPolyTime ex cnfEncoding (f i)) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => (List.finRange q).flatMap (fun i => f i x)) := by
  let hc := finiteFamilyComputable ex (symbolEncoding (Fin q)) cnfEncoding f h
  let hl := parameterizedCNFCompiler hc
  let hp := pairComputable (idComputableInPolyTime ex)
    (TM2Constants.constantComputable ex (TM2ListMap.listEncoding (symbolEncoding (Fin q))) (List.finRange q))
  exact compose (f := fun x : X => (x, List.finRange q))
    (g := fun p : X × List (Fin q) => p.2.flatMap (fun i => f i p.1)) hp hl

end ProteinFolding.SAT.CookLevinFiniteFamilyCompiler
