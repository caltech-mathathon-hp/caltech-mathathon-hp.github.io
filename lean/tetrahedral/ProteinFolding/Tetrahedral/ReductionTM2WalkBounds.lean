import ProteinFolding.Tetrahedral.ReductionTM2WalkPath

namespace ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

variable {P : Type} {adj : P × (ℕ × ℕ) → Bool}
  {p : P} {N L : ℕ} {v : ℕ → ℕ}

theorem IndexedPath.length_le_bound (hp : IndexedPath adj p N L v) : L ≤ N := by
  let f : Fin L → Fin N := fun i => ⟨v i.val, hp.bound i.val i.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.injective i.val i.isLt j.val j.isLt (congrArg Fin.val hij)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The enumerated vertex bound itself always suffices as traversal fuel. -/
theorem IndexedPath.iterate_bound (hp : IndexedPath adj p N L v) :
    (step adj)^[N] (initial p N (v 0)) = pathFinish p N L v :=
  hp.iterate_after_end N hp.length_le_bound

end ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk
