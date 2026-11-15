import ProteinFolding.Tetrahedral.ReductionDimerProvenanceAssembly

namespace ProteinFolding.Tetrahedral

namespace DimerCatalogue

structure Inclusion {α : Type} {S T : Sequence} (a : DimerCatalogue α S) (b : DimerCatalogue α T) (shift : ℕ) where
  map : a.Index → b.Index
  tag_eq : ∀ i, b.tag (map i) = a.tag i
  q_eq : ∀ i, b.q (map i) = a.q i
  offset_eq : ∀ i, (b.pre (map i)).length = shift + (a.pre i).length

namespace Inclusion

variable {α : Type} {S T U : Sequence} {a : DimerCatalogue α S} {b : DimerCatalogue α T} {c : DimerCatalogue α U}

def trans {k l : ℕ} (e : Inclusion a b k) (f : Inclusion b c l) : Inclusion a c (l + k) where
  map := fun i => f.map (e.map i)
  tag_eq := fun i => (f.tag_eq (e.map i)).trans (e.tag_eq i)
  q_eq := fun i => (f.q_eq (e.map i)).trans (e.q_eq i)
  offset_eq := by intro i; rw [f.offset_eq, e.offset_eq, Nat.add_assoc]

def appendLeft (a : DimerCatalogue α S) (b : DimerCatalogue α T)
    (hc : dimerStartCount (S ++ T) = dimerStartCount S + dimerStartCount T) : Inclusion a (a.append b hc) 0 where
  map := Sum.inl
  tag_eq := by intro i; rfl
  q_eq := by intro i; rfl
  offset_eq := by intro i; simp only [append, Nat.zero_add]

def appendRight (a : DimerCatalogue α S) (b : DimerCatalogue α T)
    (hc : dimerStartCount (S ++ T) = dimerStartCount S + dimerStartCount T) : Inclusion b (a.append b hc) S.length where
  map := Sum.inr
  tag_eq := by intro i; rfl
  q_eq := by intro i; rfl
  offset_eq := by intro i; exact List.length_append

def cast (a : DimerCatalogue α S) (h : S = T) : Inclusion a (a.cast h) 0 := by
  cases h
  exact ⟨id, fun _ => rfl, fun _ => rfl, fun _ => (Nat.zero_add _).symm⟩

def prependP (a : DimerCatalogue α (capWord S)) (n : ℕ) : Inclusion a (a.prependP n) n := by
  have hc : dimerStartCount (List.replicate n .P ++ capWord S) =
      dimerStartCount (List.replicate n .P) + dimerStartCount (capWord S) := by
    rw [count_replicate_P, Nat.zero_add]
    simpa only [List.append_nil] using dimerStartCount_P_prefix_cap n S []
  simpa only [List.length_replicate] using appendRight (silent (List.replicate n .P) (count_replicate_P n)) a hc

end Inclusion
end DimerCatalogue

namespace CataloguedBody

variable {α : Type} {P : α → ℕ → Prop}

theorem assemble_cons_count (gaps : ℕ → ℕ) (i : ℕ) (u : CataloguedBody α P) (us : List (CataloguedBody α P)) :
    dimerStartCount ((List.replicate (gaps i) .P ++ capWord u.body) ++ assembleCappedBodies gaps (i + 1) (us.map body)) =
      dimerStartCount (List.replicate (gaps i) .P ++ capWord u.body) + dimerStartCount (assembleCappedBodies gaps (i + 1) (us.map body)) := by
  cases us with
  | nil => simp [assembleCappedBodies]
  | cons v vs =>
    exact DimerCatalogue.count_append_PP _ _ (DimerCatalogue.P_prefix_capped_ends _ _)
      (assembleCappedBodies_starts_P gaps (i + 1) v.body (vs.map body))

noncomputable def assemble_head (gaps : ℕ → ℕ) (i : ℕ) (u : CataloguedBody α P) (us : List (CataloguedBody α P)) :
    DimerCatalogue.Inclusion u.catalogue (assemble gaps i (u :: us)).val (gaps i) := by
  have hc := assemble_cons_count gaps i u us
  have e := (DimerCatalogue.Inclusion.prependP u.catalogue (gaps i)).trans
    (DimerCatalogue.Inclusion.appendLeft (u.catalogue.prependP (gaps i)) (assemble gaps (i + 1) us).val hc)
  simpa only [Nat.zero_add] using e

noncomputable def assemble_tail (gaps : ℕ → ℕ) (i : ℕ) (u : CataloguedBody α P) (us : List (CataloguedBody α P)) :
    DimerCatalogue.Inclusion (assemble gaps (i + 1) us).val (assemble gaps i (u :: us)).val
      (List.replicate (gaps i) Residue.P ++ capWord u.body).length :=
  DimerCatalogue.Inclusion.appendRight (u.catalogue.prependP (gaps i)) (assemble gaps (i + 1) us).val (assemble_cons_count gaps i u us)

theorem assemble_body_inclusion (gaps : ℕ → ℕ) (i : ℕ) (us : List (CataloguedBody α P))
    (v : CataloguedBody α P) (hv : v ∈ us) :
    ∃ pre post, assembleCappedBodies gaps i (us.map body) = pre ++ capWord v.body ++ post ∧
      Nonempty (DimerCatalogue.Inclusion v.catalogue (assemble gaps i us).val pre.length) := by
  induction us generalizing i with
  | nil => simp at hv
  | cons u us ih =>
    rcases List.mem_cons.mp hv with h | hv
    · subst v
      refine ⟨List.replicate (gaps i) .P, assembleCappedBodies gaps (i + 1) (us.map body), rfl, ?_⟩
      simpa only [List.length_replicate] using Nonempty.intro (assemble_head gaps i u us)
    · obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := ih (i + 1) hv
      refine ⟨(List.replicate (gaps i) .P ++ capWord u.body) ++ pre, post, ?_, ?_⟩
      · change (List.replicate (gaps i) .P ++ capWord u.body) ++ assembleCappedBodies gaps (i + 1) (us.map body) = _
        rw [hfactor]
        simp only [List.append_assoc]
      · simpa only [List.length_append] using Nonempty.intro (e.trans (assemble_tail gaps i u us))

theorem reduction_count (gaps : ℕ → ℕ) (us : List (CataloguedBody α P)) :
    dimerStartCount ([.H, .P] ++ assembleCappedBodies gaps 0 (us.map body)) =
      dimerStartCount [.H, .P] + dimerStartCount (assembleCappedBodies gaps 0 (us.map body)) := by
  cases us with
  | nil => simp [assembleCappedBodies]
  | cons u us =>
    exact DimerCatalogue.count_append_PP _ _ ⟨[.H], rfl⟩ (assembleCappedBodies_starts_P gaps 0 u.body (us.map body))

noncomputable def reduction_inclusion (gaps : ℕ → ℕ) (us : List (CataloguedBody α P)) :
    DimerCatalogue.Inclusion (assemble gaps 0 us).val (reduction gaps us).val 2 :=
  DimerCatalogue.Inclusion.appendRight (DimerCatalogue.silent [.H, .P] (by decide)) (assemble gaps 0 us).val (reduction_count gaps us)

theorem reduction_body_inclusion (gaps : ℕ → ℕ) (us : List (CataloguedBody α P))
    (v : CataloguedBody α P) (hv : v ∈ us) :
    ∃ pre post, assembleReductionWord gaps (us.map body) = pre ++ capWord v.body ++ post ∧
      Nonempty (DimerCatalogue.Inclusion v.catalogue (reduction gaps us).val pre.length) := by
  obtain ⟨pre, post, hfactor, ⟨e⟩⟩ := assemble_body_inclusion gaps 0 us v hv
  refine ⟨[.H, .P] ++ pre, post, ?_, ?_⟩
  · unfold assembleReductionWord
    rw [hfactor]
    simp only [List.append_assoc]
  · simpa only [List.length_append, List.length_cons, List.length_nil] using Nonempty.intro (e.trans (reduction_inclusion gaps us))

end CataloguedBody

end ProteinFolding.Tetrahedral
