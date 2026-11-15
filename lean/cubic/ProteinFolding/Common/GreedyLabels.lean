import Mathlib.Data.List.Chain
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card

/-! A finite greedy-label lemma: at least two permitted labels at every
position suffice to choose consecutive distinct labels, while avoiding an
arbitrary prescribed terminal label. This is used for exterior edge-path
attachments and does not assume any geometric or complexity result. -/

namespace ProteinFolding.GreedyLabels

variable {D : Type} [DecidableEq D]

theorem exists_mem_ne (s : Finset D) (hs : 2 ≤ s.card) (forbidden : D) :
    ∃ d ∈ s, d ≠ forbidden := by
  classical
  by_contra hn
  have hall : ∀ d ∈ s, d = forbidden := by
    intro d hd
    by_contra hne
    exact hn ⟨d, hd, hne⟩
  have hsub : s ⊆ {forbidden} := by intro d hd; simpa using hall d hd
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  omega

theorem list_labels (sets : List (Finset D)) (htwo : ∀ s ∈ sets, 2 ≤ s.card) (terminal : D) :
    ∃ labels : List D, List.Forall₂ (fun d s => d ∈ s) labels sets ∧
      (labels ++ [terminal]).IsChain (· ≠ ·) := by
  classical
  induction sets with
  | nil => exact ⟨[], .nil, .singleton terminal⟩
  | cons s sets ih =>
    obtain ⟨labels, hp, hc⟩ := ih (fun s hs => htwo s (by simp [hs]))
    obtain ⟨d, hd, hne⟩ := exists_mem_ne s (htwo s (by simp)) (labels.headD terminal)
    refine ⟨d :: labels, .cons hd hp, ?_⟩
    cases labels with
    | nil => simpa using (List.IsChain.singleton terminal).cons_cons hne
    | cons e labels =>
      exact hc.cons_cons (by simpa using hne)

/-- A function version with an extra terminal position. The last label is
prescribed, every earlier label is permitted, and all neighbours differ. -/
theorem finite_labels (N : ℕ) (allowed : Fin N → Finset D) (htwo : ∀ i, 2 ≤ (allowed i).card)
    (terminal : D) : ∃ f : Fin (N + 1) → D,
      f ⟨N, by omega⟩ = terminal ∧
        (∀ i : Fin N, f i.castSucc ∈ allowed i) ∧
        (∀ i : Fin N, f i.castSucc ≠ f i.succ) := by
  classical
  obtain ⟨labels, hp, hc⟩ := list_labels (List.ofFn allowed)
    (by intro s hs; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs; exact htwo i) terminal
  have hlen : labels.length = N := by simpa using hp.length_eq
  let sequence := labels ++ [terminal]
  have hslen : sequence.length = N + 1 := by simp [sequence, hlen]
  let f : Fin (N + 1) → D := fun j => sequence.get ⟨j.val, by have := j.isLt; omega⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · dsimp [f, sequence]
    rw [List.getElem_append_right (by omega)]
    simp [hlen]
  · intro i
    have hi : i.val < labels.length := by have := i.isLt; omega
    have hio : i.val < (List.ofFn allowed).length := by rw [List.length_ofFn]; exact i.isLt
    have hm := hp.get hi hio
    have his : i.val < (labels ++ [terminal]).length := by simp only [List.length_append, List.length_singleton, hlen]; omega
    change (labels ++ [terminal])[i.val]'his ∈ allowed i
    rw [List.getElem_append_left hi]
    simpa only [List.get_eq_getElem, List.getElem_ofFn] using hm
  · intro i
    have h := (List.isChain_iff_get.mp hc) i.val (by
      change i.val + 1 < sequence.length
      rw [hslen]
      have := i.isLt
      omega)
    exact h

end ProteinFolding.GreedyLabels
