import ProteinFolding.Tetrahedral.FrameForcingActualChains

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

/-- A finite catalogue of declared whole capped chains, with their exact
positions. Interval separation retains the declared maximal unit identity;
the count equation certifies that no actual PHHP occurrence is omitted. -/
structure DimerCatalogue (α : Type) (S : Sequence) where
  Index : Type
  finiteIndex : Fintype Index
  q : Index → ℕ
  tag : Index → α
  pre : Index → Sequence
  post : Index → Sequence
  factor : ∀ i, S = pre i ++ capWord (dimerChain (q i)) ++ post i
  separate : ∀ i j, i ≠ j →
    (pre i).length + (capWord (dimerChain (q i))).length ≤ (pre j).length ∨
      (pre j).length + (capWord (dimerChain (q j))).length ≤ (pre i).length
  count : (@Finset.univ Index finiteIndex).sum q = dimerStartCount S

namespace DimerCatalogue

variable {α : Type} {S T : Sequence}

def chain (tag : α) (q : ℕ) : DimerCatalogue α (capWord (dimerChain q)) where
  Index := Unit
  finiteIndex := inferInstance
  q := fun _ => q
  tag := fun _ => tag
  pre := fun _ => []
  post := fun _ => []
  factor := by intro i; simp
  separate := by intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  count := by simp

def silent (S : Sequence) (hzero : dimerStartCount S = 0) : DimerCatalogue α S where
  Index := Empty
  finiteIndex := inferInstance
  q := Empty.elim
  tag := Empty.elim
  pre := Empty.elim
  post := Empty.elim
  factor := by intro i; exact Empty.elim i
  separate := by intro i; exact Empty.elim i
  count := by simpa using hzero.symm

noncomputable def append (a : DimerCatalogue α S) (b : DimerCatalogue α T)
    (hc : dimerStartCount (S ++ T) = dimerStartCount S + dimerStartCount T) :
    DimerCatalogue α (S ++ T) := by
  letI := a.finiteIndex
  letI := b.finiteIndex
  exact {
    Index := a.Index ⊕ b.Index
    finiteIndex := inferInstance
    q := Sum.elim a.q b.q
    tag := Sum.elim a.tag b.tag
    pre := fun i => match i with
      | .inl i => a.pre i
      | .inr i => S ++ b.pre i
    post := fun i => match i with
      | .inl i => a.post i ++ T
      | .inr i => b.post i
    factor := by
      intro i
      cases i with
      | inl i => simpa only [List.append_assoc] using congrArg (fun u : Sequence => u ++ T) (a.factor i)
      | inr i => simpa only [List.append_assoc] using congrArg (fun u : Sequence => S ++ u) (b.factor i)
    separate := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact a.separate i j (fun h => hij (congrArg Sum.inl h))
        | inr j =>
          left
          have h := congrArg List.length (a.factor i)
          simp only [Sum.elim_inl, Sum.elim_inr, List.length_append] at h ⊢
          omega
      | inr i =>
        cases j with
        | inl j =>
          right
          have h := congrArg List.length (a.factor j)
          simp only [Sum.elim_inl, Sum.elim_inr, List.length_append] at h ⊢
          omega
        | inr j =>
          have h := b.separate i j (fun h => hij (congrArg Sum.inr h))
          simp only [Sum.elim_inl, Sum.elim_inr, List.length_append]
          omega
    count := by
      change (∑ i : a.Index ⊕ b.Index, Sum.elim a.q b.q i) = _
      rw [Fintype.sum_sum_type]
      exact (congrArg₂ (· + ·) a.count b.count).trans hc.symm }

noncomputable def cast (a : DimerCatalogue α S) (h : S = T) : DimerCatalogue α T := h ▸ a

def occurrence (c : DimerCatalogue α S) (a : Σ i : c.Index, Fin (c.q i)) : DimerOccurrence S :=
  factorDimerOccurrence S (c.pre a.1) (c.post a.1) (c.q a.1) (c.factor a.1) a.2

theorem occurrence_val (c : DimerCatalogue α S) (a : Σ i : c.Index, Fin (c.q i)) :
    (c.occurrence a).val = (c.pre a.1).length + 5 * a.2.val := rfl

theorem occurrence_injective (c : DimerCatalogue α S) : Function.Injective c.occurrence := by
  rintro ⟨i, a⟩ ⟨j, b⟩ heq
  have hv := congrArg Subtype.val heq
  change (c.pre i).length + 5 * a.val = (c.pre j).length + 5 * b.val at hv
  by_cases hij : i = j
  · subst j
    have hab : a = b := by apply Fin.ext; omega
    subst b
    rfl
  · have ha := (List.getElem?_eq_some_iff.mp (capped_dimer_start (c.q i) a.val a.isLt).1).choose
    have hb := (List.getElem?_eq_some_iff.mp (capped_dimer_start (c.q j) b.val b.isLt).1).choose
    have hs := c.separate i j hij
    omega

theorem occurrence_bijective (c : DimerCatalogue α S) : Function.Bijective c.occurrence := by
  letI := c.finiteIndex
  apply (Fintype.bijective_iff_injective_and_card c.occurrence).2
  refine ⟨c.occurrence_injective, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_coe, dimerStartIndices_card]
  exact c.count

theorem occurrence_complete (c : DimerCatalogue α S) (a : DimerOccurrence S) :
    ∃ (i : c.Index) (j : Fin (c.q i)), c.occurrence ⟨i, j⟩ = a := by
  obtain ⟨⟨i, j⟩, h⟩ := c.occurrence_bijective.2 a
  exact ⟨i, j, h⟩

theorem starts_lt (c : DimerCatalogue α S) (i : c.Index) (j : Fin (c.q i)) :
    (c.pre i).length + 5 * j.val < (c.pre i).length + (capWord (dimerChain (c.q i))).length := by
  have h := (List.getElem?_eq_some_iff.mp (capped_dimer_start (c.q i) j.val j.isLt).1).choose
  omega

end DimerCatalogue

end ProteinFolding.Tetrahedral
