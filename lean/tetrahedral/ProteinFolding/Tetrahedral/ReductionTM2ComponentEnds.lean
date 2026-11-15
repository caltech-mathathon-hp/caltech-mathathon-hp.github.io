import ProteinFolding.Tetrahedral.FinitePathComponents

namespace ProteinFolding.Tetrahedral.ReductionTM2

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem componentFold_first_pos (c : G.ConnectedComponent) :
    (componentFold G c).pos ⟨0, by omega⟩ = (componentMaxPath G c).start := by
  change (componentMaxPath G c).walk.getVert 0 = _
  exact SimpleGraph.Walk.getVert_zero _

theorem componentFold_last_pos (c : G.ConnectedComponent) :
    (componentFold G c).pos ⟨(componentMaxPath G c).walk.length, by omega⟩ = (componentMaxPath G c).finish := by
  change (componentMaxPath G c).walk.getVert (componentMaxPath G c).walk.length = _
  exact SimpleGraph.Walk.getVert_length _

theorem componentFold_last_sub_pos (c : G.ConnectedComponent) :
    (componentFold G c).pos ⟨(componentMaxPath G c).walk.length + 1 - 1, by omega⟩ =
      (componentMaxPath G c).finish := by
  change (componentMaxPath G c).walk.getVert ((componentMaxPath G c).walk.length + 1 - 1) = _
  have hl : (componentMaxPath G c).walk.length + 1 - 1 = (componentMaxPath G c).walk.length := by omega
  rw [hl]
  exact SimpleGraph.Walk.getVert_length _

end ProteinFolding.Tetrahedral.ReductionTM2
