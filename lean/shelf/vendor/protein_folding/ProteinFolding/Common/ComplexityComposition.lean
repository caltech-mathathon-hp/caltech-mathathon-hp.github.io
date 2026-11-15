import ProteinFolding.Common.ComplexityLemmas
import ProteinFolding.Common.TM2CompositionPoly

/-! Unconditional Karp transitivity and NP-hardness transfer using the proved
finite-machine composition construction. Cook--Levin is an explicit hypothesis
only where SAT hardness is used. -/

namespace ProteinFolding

open Computability Turing

variable {A B D : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {ed : FinEncoding D} {L : A → Prop} {M : B → Prop} {N : D → Prop}

theorem karpReduces_trans (hLM : KarpReduces ea eb L M) (hMN : KarpReduces eb ed M N) :
    KarpReduces ea ed L N := by
  apply karpReduces_trans_of_composition _ hLM hMN
  intro f g hf hg
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact ⟨TM2CompositionPoly.compose hf hg⟩

theorem npHard_of_karpReduces (hL : NPHard ea L) (hLM : KarpReduces ea eb L M) :
    NPHard eb M := by
  intro Source eSource K hK
  exact karpReduces_trans (hL Source eSource K hK) hLM

theorem npHard_of_cookLevin_reduction (hCL : SAT.CookLevin)
    (hSAT : KarpReduces SAT.cnfEncoding ea SAT.Satisfiable L) : NPHard ea L :=
  npHard_of_karpReduces hCL hSAT

theorem npComplete_of_cookLevin_reduction (hCL : SAT.CookLevin)
    (hSAT : KarpReduces SAT.cnfEncoding ea SAT.Satisfiable L) (hNP : InNP ea L) :
    NPComplete ea L :=
  ⟨hNP, npHard_of_cookLevin_reduction hCL hSAT⟩

end ProteinFolding
