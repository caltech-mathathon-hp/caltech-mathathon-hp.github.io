import ProteinFolding.Tetrahedral.ReductionDimerProvenanceAssembly

namespace ProteinFolding.Tetrahedral

namespace DimerCatalogue

variable {α : Type} {S T : Sequence}

def weightSum (c : DimerCatalogue α S) (F : α → ℕ → ℕ) : ℕ :=
  (@Finset.univ c.Index c.finiteIndex).sum (fun i => F (c.tag i) (c.q i))

theorem weightSum_chain (tag : α) (q : ℕ) (F : α → ℕ → ℕ) :
    (chain tag q).weightSum F = F tag q := by simp [weightSum, chain]

theorem weightSum_silent (S : Sequence) (hz : dimerStartCount S = 0) (F : α → ℕ → ℕ) :
    (silent S hz).weightSum F = 0 := by simp [weightSum, silent]

theorem weightSum_append (a : DimerCatalogue α S) (b : DimerCatalogue α T)
    (hc : dimerStartCount (S ++ T) = dimerStartCount S + dimerStartCount T) (F : α → ℕ → ℕ) :
    (a.append b hc).weightSum F = a.weightSum F + b.weightSum F := by
  letI := a.finiteIndex
  letI := b.finiteIndex
  change (∑ i : a.Index ⊕ b.Index, F (Sum.elim a.tag b.tag i) (Sum.elim a.q b.q i)) = _
  rw [Fintype.sum_sum_type]
  rfl

theorem weightSum_cast (a : DimerCatalogue α S) (h : S = T) (F : α → ℕ → ℕ) :
    (a.cast h).weightSum F = a.weightSum F := by cases h; rfl

theorem weightSum_prependP (c : DimerCatalogue α (capWord S)) (n : ℕ) (F : α → ℕ → ℕ) :
    (c.prependP n).weightSum F = c.weightSum F := by
  unfold prependP
  rw [weightSum_append, weightSum_silent, Nat.zero_add]

end DimerCatalogue

namespace CataloguedBody

variable {α : Type} {P : α → ℕ → Prop}

theorem assemble_weightSum (gaps : ℕ → ℕ) (i : ℕ) (us : List (CataloguedBody α P)) (F : α → ℕ → ℕ) :
    (assemble gaps i us).val.weightSum F = (us.map (fun u => u.catalogue.weightSum F)).sum := by
  induction us generalizing i with
  | nil => exact DimerCatalogue.weightSum_silent [] rfl F
  | cons u us ih =>
    have hc : dimerStartCount ((List.replicate (gaps i) .P ++ capWord u.body) ++
        assembleCappedBodies gaps (i + 1) (us.map body)) =
        dimerStartCount (List.replicate (gaps i) .P ++ capWord u.body) +
          dimerStartCount (assembleCappedBodies gaps (i + 1) (us.map body)) := by
      cases us with
      | nil => simp only [List.map_nil, assembleCappedBodies, List.append_nil, dimerStartCount_nil, Nat.add_zero]
      | cons v vs =>
        exact DimerCatalogue.count_append_PP _ _ (DimerCatalogue.P_prefix_capped_ends _ _)
          (assembleCappedBodies_starts_P gaps (i + 1) v.body (vs.map body))
    change ((u.catalogue.prependP (gaps i)).append (assemble gaps (i + 1) us).val hc).weightSum F = _
    rw [DimerCatalogue.weightSum_append, DimerCatalogue.weightSum_prependP, ih]
    rfl

theorem reduction_weightSum (gaps : ℕ → ℕ) (us : List (CataloguedBody α P)) (F : α → ℕ → ℕ) :
    (reduction gaps us).val.weightSum F = (us.map (fun u => u.catalogue.weightSum F)).sum := by
  have hc : dimerStartCount ([.H, .P] ++ assembleCappedBodies gaps 0 (us.map body)) =
      dimerStartCount [.H, .P] + dimerStartCount (assembleCappedBodies gaps 0 (us.map body)) := by
    cases us with
    | nil => simp [assembleCappedBodies]
    | cons u us =>
      exact DimerCatalogue.count_append_PP _ _ ⟨[.H], rfl⟩
        (assembleCappedBodies_starts_P gaps 0 u.body (us.map body))
  change ((DimerCatalogue.silent [.H, .P] (by decide)).append (assemble gaps 0 us).val hc).weightSum F = _
  rw [DimerCatalogue.weightSum_append, DimerCatalogue.weightSum_silent, Nat.zero_add, assemble_weightSum]

end CataloguedBody

end ProteinFolding.Tetrahedral
