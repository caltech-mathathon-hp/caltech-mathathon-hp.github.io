import ProteinFolding.Tetrahedral.FinitePathComponents

/-! The local non-isolation and no-two-leaf-edge conditions ensure that
the component paths have at least three vertices. -/

namespace ProteinFolding.Tetrahedral

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MaximalComponentPath.length_pos {c : V} (p : MaximalComponentPath G c)
    (hnonzero : 1 ≤ G.degree p.start) : 1 ≤ p.walk.length := by
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj p.start).mp (by omega)
  have hp : (Walk.cons hw (.nil : G.Walk w w)).IsPath := by simp [hw.ne]
  have h := p.maximal (Walk.cons hw .nil) p.reachable_start hp
  simpa only [Walk.length_cons, Walk.length_nil] using h

theorem MaximalComponentPath.vertex_count_ge_three {c : V} (p : MaximalComponentPath G c)
    (hdegree : ∀ v, G.degree v ≤ 2) (hacyclic : G.IsAcyclic)
    (hnonzero : ∀ v, 1 ≤ G.degree v)
    (hnoPair : ∀ a b, G.Adj a b → G.degree a = 1 → G.degree b ≠ 1) :
    3 ≤ p.walk.length + 1 := by
  have hpos := p.length_pos G (hnonzero p.start)
  have hends := p.endpoint_degrees G hdegree hacyclic hnonzero
  have hnotone : p.walk.length ≠ 1 := by
    intro hlen
    have hadj := p.walk.adj_of_length_eq_one hlen
    exact hnoPair p.start p.finish hadj hends.1 hends.2
  omega

theorem componentPath_vertex_count_ge_three (hdegree : ∀ v, G.degree v ≤ 2)
    (hacyclic : G.IsAcyclic) (hnonzero : ∀ v, 1 ≤ G.degree v)
    (hnoPair : ∀ a b, G.Adj a b → G.degree a = 1 → G.degree b ≠ 1)
    (c : G.ConnectedComponent) : 3 ≤ (componentMaxPath G c).walk.length + 1 :=
  (componentMaxPath G c).vertex_count_ge_three G hdegree hacyclic hnonzero hnoPair

end ProteinFolding.Tetrahedral
