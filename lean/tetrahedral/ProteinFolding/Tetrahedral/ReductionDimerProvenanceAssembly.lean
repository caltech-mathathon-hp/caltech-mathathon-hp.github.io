import ProteinFolding.Tetrahedral.ReductionDimerProvenanceCatalogue

namespace ProteinFolding.Tetrahedral

namespace DimerCatalogue

variable {α : Type} {S T : Sequence}

def Satisfies (c : DimerCatalogue α S) (P : α → ℕ → Prop) : Prop := ∀ i, P (c.tag i) (c.q i)

theorem satisfies_chain (P : α → ℕ → Prop) (tag : α) (q : ℕ) (h : P tag q) :
    (chain tag q).Satisfies P := fun _ => h

theorem satisfies_silent (P : α → ℕ → Prop) (S : Sequence) (hz : dimerStartCount S = 0) :
    (silent S hz).Satisfies P := by intro i; exact Empty.elim i

theorem satisfies_append (a : DimerCatalogue α S) (b : DimerCatalogue α T)
    (hc : dimerStartCount (S ++ T) = dimerStartCount S + dimerStartCount T)
    (P : α → ℕ → Prop) (ha : a.Satisfies P) (hb : b.Satisfies P) :
    (a.append b hc).Satisfies P := by
  intro i
  cases i with
  | inl i => exact ha i
  | inr i => exact hb i

theorem satisfies_cast (a : DimerCatalogue α S) (h : S = T) (P : α → ℕ → Prop) (ha : a.Satisfies P) :
    (a.cast h).Satisfies P := by cases h; exact ha

theorem count_append_PP (u v : Sequence)
    (hu : ∃ x, u = x ++ [.P]) (hv : ∃ y, v = .P :: y) :
    dimerStartCount (u ++ v) = dimerStartCount u + dimerStartCount v := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  simpa only [List.append_assoc, List.singleton_append] using dimerStartCount_PP_split x y

theorem capped_starts_P (u : Sequence) : ∃ v, capWord u = .P :: v := ⟨u ++ [.P], rfl⟩
theorem capped_ends_P (u : Sequence) : ∃ v, capWord u = v ++ [.P] := ⟨.P :: u, rfl⟩

theorem P_prefix_capped_starts (n : ℕ) (u : Sequence) :
    ∃ v, List.replicate n .P ++ capWord u = .P :: v := by
  cases n with
  | zero => exact capped_starts_P u
  | succ n => exact ⟨List.replicate n .P ++ capWord u, by simp [List.replicate_succ]⟩

theorem P_prefix_capped_ends (n : ℕ) (u : Sequence) :
    ∃ v, List.replicate n .P ++ capWord u = v ++ [.P] := by
  exact ⟨List.replicate n .P ++ .P :: u, by simp only [capWord, List.append_assoc, List.cons_append]⟩

theorem count_replicate_P (n : ℕ) : dimerStartCount (List.replicate n .P) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := dimerStartCount_replicate_P n []
    simpa only [List.append_nil, dimerStartCount_singleton] using h

noncomputable def prependP (c : DimerCatalogue α (capWord S)) (n : ℕ) :
    DimerCatalogue α (List.replicate n .P ++ capWord S) :=
  (silent (List.replicate n .P) (count_replicate_P n)).append c (by
    rw [count_replicate_P, Nat.zero_add]
    simpa only [List.append_nil] using dimerStartCount_P_prefix_cap n S [])

theorem satisfies_prependP (c : DimerCatalogue α (capWord S)) (n : ℕ)
    (P : α → ℕ → Prop) (hc : c.Satisfies P) : (c.prependP n).Satisfies P :=
  satisfies_append _ _ _ P (satisfies_silent P _ _) hc

end DimerCatalogue

structure CataloguedBody (α : Type) (P : α → ℕ → Prop) where
  body : Sequence
  catalogue : DimerCatalogue α (capWord body)
  property : catalogue.Satisfies P

namespace CataloguedBody

variable {α : Type} {P : α → ℕ → Prop}

def chain (tag : α) (q : ℕ) (h : P tag q) : CataloguedBody α P :=
  ⟨dimerChain q, DimerCatalogue.chain tag q, DimerCatalogue.satisfies_chain P tag q h⟩

def silent (body : Sequence) (hz : dimerStartCount (capWord body) = 0) : CataloguedBody α P :=
  ⟨body, DimerCatalogue.silent _ hz, DimerCatalogue.satisfies_silent P _ hz⟩

noncomputable def assemble (gaps : ℕ → ℕ) (i : ℕ) (us : List (CataloguedBody α P)) :
    {c : DimerCatalogue α (assembleCappedBodies gaps i (us.map body)) // c.Satisfies P} := by
  induction us generalizing i with
  | nil => exact ⟨DimerCatalogue.silent [] rfl, DimerCatalogue.satisfies_silent P [] rfl⟩
  | cons u us ih =>
    let a := u.catalogue.prependP (gaps i)
    let b := ih (i + 1)
    have hc : dimerStartCount ((List.replicate (gaps i) .P ++ capWord u.body) ++
        assembleCappedBodies gaps (i + 1) (us.map body)) =
        dimerStartCount (List.replicate (gaps i) .P ++ capWord u.body) +
          dimerStartCount (assembleCappedBodies gaps (i + 1) (us.map body)) := by
      cases us with
      | nil => simp only [List.map_nil, assembleCappedBodies, List.append_nil, dimerStartCount_nil, Nat.add_zero]
      | cons v vs =>
        exact DimerCatalogue.count_append_PP _ _ (DimerCatalogue.P_prefix_capped_ends _ _)
          (assembleCappedBodies_starts_P gaps (i + 1) v.body (vs.map body))
    let c := a.append b.val hc
    change {c : DimerCatalogue α ((List.replicate (gaps i) .P ++ capWord u.body) ++
      assembleCappedBodies gaps (i + 1) (us.map body)) // c.Satisfies P}
    exact ⟨c, DimerCatalogue.satisfies_append a b.val hc P
      (DimerCatalogue.satisfies_prependP u.catalogue (gaps i) P u.property) b.property⟩

noncomputable def reduction (gaps : ℕ → ℕ) (us : List (CataloguedBody α P)) :
    {c : DimerCatalogue α (assembleReductionWord gaps (us.map body)) // c.Satisfies P} := by
  let a : DimerCatalogue α [.H, .P] := DimerCatalogue.silent _ (by decide)
  let b := assemble gaps 0 us
  have hc : dimerStartCount ([.H, .P] ++ assembleCappedBodies gaps 0 (us.map body)) =
      dimerStartCount [.H, .P] + dimerStartCount (assembleCappedBodies gaps 0 (us.map body)) := by
    cases us with
    | nil => simp [assembleCappedBodies]
    | cons u us =>
      exact DimerCatalogue.count_append_PP _ _ ⟨[.H], rfl⟩
        (assembleCappedBodies_starts_P gaps 0 u.body (us.map body))
  exact ⟨a.append b.val hc, DimerCatalogue.satisfies_append a b.val hc P
    (DimerCatalogue.satisfies_silent P _ _) b.property⟩

end CataloguedBody

end ProteinFolding.Tetrahedral
