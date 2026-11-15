import ProteinFolding.Square.Geometry

/-! Losses as actual unordered lattice edges, with no duplicate representatives. -/

namespace ProteinFolding.Square

def IsHydrophobicSite (S : Sequence) (f : Fold squareLattice S.length) (x : Site) : Prop :=
  ∃ i, S.get i = Residue.H ∧ f.pos i = x

def IsBackboneEdge (S : Sequence) (f : Fold squareLattice S.length) (e : Sym2 Site) : Prop :=
  ∃ i j, i.val + 1 = j.val ∧ e = s(f.pos i, f.pos j)

/-- Exactly one endpoint holds H. Ordering the two endpoints here is existential;
the object being classified is an unordered pair. -/
def IsLossEdge (S : Sequence) (f : Fold squareLattice S.length) (e : Sym2 Site) : Prop :=
  ∃ x y, e = s(x, y) ∧ squareLattice.Adj x y ∧
    IsHydrophobicSite S f x ∧ ¬ IsHydrophobicSite S f y ∧ ¬ IsBackboneEdge S f e

def lossEdge (S : Sequence) (f : Fold squareLattice S.length)
    (a : Fin S.length × Fin 4) : Sym2 Site :=
  s(f.pos a.1, step (f.pos a.1) a.2)

theorem mem_lossEdges (S : Sequence) (f : Fold squareLattice S.length)
    (a : Fin S.length × Fin 4) :
    a ∈ lossEdges S f ↔ S.get a.1 = Residue.H ∧
      (∀ j, S.get j = Residue.H → f.pos j ≠ step (f.pos a.1) a.2) ∧
      (∀ j, a.1.val + 1 = j.val ∨ j.val + 1 = a.1.val →
        f.pos j ≠ step (f.pos a.1) a.2) := by
  simp [lossEdges, hydrophobicIndices]

theorem lossEdge_isLoss (S : Sequence) (f : Fold squareLattice S.length)
    {a : Fin S.length × Fin 4} (ha : a ∈ lossEdges S f) :
    IsLossEdge S f (lossEdge S f a) := by
  obtain ⟨hh, hn, hb⟩ := (mem_lossEdges S f a).1 ha
  refine ⟨_, _, rfl, step_adj _ _, ⟨a.1, hh, rfl⟩, ?_, ?_⟩
  · rintro ⟨j, hj, he⟩
    exact hn j hj he
  · rintro ⟨i, j, hij, he⟩
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · have hi' := f.injective_pos hi
      exact hb j (Or.inl (hi' ▸ hij)) hj.symm
    · have hj' := f.injective_pos hj
      exact hb i (Or.inr (hj' ▸ hij)) hi.symm

theorem isLoss_exists_direction (S : Sequence) (f : Fold squareLattice S.length)
    {e : Sym2 Site} (he : IsLossEdge S f e) :
    ∃ a ∈ lossEdges S f, lossEdge S f a = e := by
  obtain ⟨x, y, rfl, hxy, ⟨i, hi, rfl⟩, hn, hb⟩ := he
  obtain ⟨d, rfl⟩ := adj_step hxy
  refine ⟨(i, d), (mem_lossEdges S f _).2 ⟨hi, ?_, ?_⟩, rfl⟩
  · intro j hj he
    exact hn ⟨j, hj, he⟩
  · intro j hj he
    apply hb
    rcases hj with hj | hj
    · exact ⟨i, j, hj, by rw [he]⟩
    · exact ⟨j, i, hj, by rw [he, Sym2.eq_swap]⟩

theorem lossEdge_injective (S : Sequence) (f : Fold squareLattice S.length) :
    Set.InjOn (lossEdge S f) (lossEdges S f) := by
  intro a ha b hb he
  obtain ⟨hha, hna, _⟩ := (mem_lossEdges S f a).1 ha
  obtain ⟨hhb, _, _⟩ := (mem_lossEdges S f b).1 hb
  rcases Sym2.eq_iff.mp he with ⟨hi, hd⟩ | ⟨hi, hd⟩
  · have hi' := f.injective_pos hi
    apply Prod.ext hi'
    apply step_inj (f.pos a.1)
    simpa only [hi'] using hd
  · exact False.elim (hna b.1 hhb hd.symm)

/-- The finite set of all paper losses, now represented as unordered edges. -/
def latticeLossEdges (S : Sequence) (f : Fold squareLattice S.length) : Finset (Sym2 Site) :=
  (lossEdges S f).image (lossEdge S f)

theorem mem_latticeLossEdges (S : Sequence) (f : Fold squareLattice S.length) (e : Sym2 Site) :
    e ∈ latticeLossEdges S f ↔ IsLossEdge S f e := by
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact lossEdge_isLoss S f ha
  · intro he
    exact Finset.mem_image.mpr (isLoss_exists_direction S f he)

theorem lossCount_eq_card_latticeLossEdges (S : Sequence) (f : Fold squareLattice S.length) :
    lossCount S f = (latticeLossEdges S f).card := by
  exact (Finset.card_image_of_injOn (lossEdge_injective S f)).symm

end ProteinFolding.Square
