import ProteinFolding.Common.CookLevin

/-!
# Initial complexity infrastructure

These lemmas use the frozen framework. Machine composition, its output-length
bound, and transitivity of Karp reductions remain to be established.
-/

namespace ProteinFolding

open Computability Turing

variable {A B C : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {ec : FinEncoding C} {L L' : A → Prop} {M M' : B → Prop}

theorem karpReduces_refl (ea : FinEncoding A) (L : A → Prop) :
    KarpReduces ea ea L L :=
  ⟨id, ⟨idComputableInPolyTime ea⟩, fun _ => Iff.rfl⟩

theorem polyTimeDecidable_congr (h : ∀ x, L x ↔ L' x)
    (hL : PolyTimeDecidable ea L) : PolyTimeDecidable ea L' := by
  obtain ⟨f, hf, hcorrect⟩ := hL
  exact ⟨f, hf, fun x => (hcorrect x).trans (h x)⟩

theorem inNP_congr (h : ∀ x, L x ↔ L' x) (hL : InNP ea L) : InNP ea L' := by
  obtain ⟨Cert, eCert, hsurj, p, R, hR, hcorrect⟩ := hL
  exact ⟨Cert, eCert, hsurj, p, R, hR, fun x => (h x).symm.trans (hcorrect x)⟩

theorem karpReduces_congr (hL : ∀ x, L x ↔ L' x) (hM : ∀ y, M y ↔ M' y)
    (h : KarpReduces ea eb L M) : KarpReduces ea eb L' M' := by
  obtain ⟨f, hf, hcorrect⟩ := h
  exact ⟨f, hf, fun x => (hL x).symm.trans ((hcorrect x).trans (hM (f x)))⟩

theorem npHard_congr (h : ∀ x, L x ↔ L' x) (hL : NPHard ea L) : NPHard ea L' := by
  intro Source eSource K hK
  exact karpReduces_congr (fun _ => Iff.rfl) h (hL Source eSource K hK)

theorem npComplete_congr (h : ∀ x, L x ↔ L' x) (hL : NPComplete ea L) :
    NPComplete ea L' :=
  ⟨inNP_congr h hL.1, npHard_congr h hL.2⟩

theorem wordEncoding_length (Alphabet : Type) [Fintype Alphabet] (w : List Alphabet) :
    ((wordEncoding Alphabet).encode w).length = w.length := rfl

theorem pairEncoding_length (ea : FinEncoding A) (eb : FinEncoding B) (x : A) (y : B) :
    ((pairEncoding ea eb).encode (x, y)).length =
      (ea.encode x).length + (eb.encode y).length + 1 := by
  simp [pairEncoding, Nat.add_comm, Nat.add_left_comm]

/-- Reuse an actual composition construction when one has been proved.
The additional hypothesis is deliberately explicit; this is not an unconditional
transitivity theorem and is not used to assert any final HP result. -/
theorem karpReduces_trans_of_composition
    (hcomp : ∀ (f : A → B) (g : B → C),
      Nonempty (TM2ComputableInPolyTime ea eb f) →
      Nonempty (TM2ComputableInPolyTime eb ec g) →
      Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)))
    {N : C → Prop} (hLM : KarpReduces ea eb L M) (hMN : KarpReduces eb ec M N) :
    KarpReduces ea ec L N := by
  obtain ⟨f, hf, hcorrectF⟩ := hLM
  obtain ⟨g, hg, hcorrectG⟩ := hMN
  exact ⟨g ∘ f, hcomp f g hf hg, fun x => (hcorrectF x).trans (hcorrectG (f x))⟩

/-- Conditional transfer from the supplied Cook--Levin hypothesis.
Both the SAT reduction and the missing machine-composition construction remain
explicit inputs. This is an interim result, not an HP hardness proof. -/
theorem npHard_of_cookLevin_reduction_of_composition
    (hCL : SAT.CookLevin)
    (hSAT : KarpReduces SAT.cnfEncoding ea SAT.Satisfiable L)
    (hcomp : ∀ (Source : Type) (eSource : FinEncoding Source)
      (f : Source → SAT.CNF) (g : SAT.CNF → A),
      Nonempty (TM2ComputableInPolyTime eSource SAT.cnfEncoding f) →
      Nonempty (TM2ComputableInPolyTime SAT.cnfEncoding ea g) →
      Nonempty (TM2ComputableInPolyTime eSource ea (g ∘ f))) : NPHard ea L := by
  intro Source eSource K hK
  exact karpReduces_trans_of_composition (hcomp Source eSource)
    (hCL Source eSource K hK) hSAT

end ProteinFolding
